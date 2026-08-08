package dev.baritoneweb.bridge;

import com.sun.net.httpserver.Headers;
import com.sun.net.httpserver.HttpExchange;
import com.sun.net.httpserver.HttpServer;
import net.minecraftforge.fml.common.Mod;

import java.io.ByteArrayInputStream;
import java.io.ByteArrayOutputStream;
import java.io.IOException;
import java.io.InputStream;
import java.io.PrintWriter;
import java.io.StringWriter;
import java.lang.reflect.Field;
import java.lang.reflect.InvocationTargetException;
import java.lang.reflect.Method;
import java.lang.reflect.Modifier;
import java.net.InetSocketAddress;
import java.net.URLDecoder;
import java.nio.ByteBuffer;
import java.nio.ByteOrder;
import java.nio.IntBuffer;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.StandardOpenOption;
import java.time.Instant;
import java.time.ZoneId;
import java.time.format.DateTimeFormatter;
import java.security.MessageDigest;
import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.HexFormat;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;
import java.util.UUID;
import java.util.concurrent.CompletableFuture;
import java.util.concurrent.ConcurrentHashMap;
import java.util.concurrent.Executors;
import java.util.concurrent.LinkedBlockingQueue;
import java.util.concurrent.Executor;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.ScheduledExecutorService;
import java.util.concurrent.TimeUnit;
import java.util.concurrent.TimeoutException;
import java.util.concurrent.atomic.AtomicBoolean;
import java.util.concurrent.atomic.AtomicLong;
import java.util.regex.Matcher;
import java.util.regex.Pattern;
import java.util.jar.JarEntry;
import java.util.jar.JarFile;
import javax.imageio.ImageIO;
import java.awt.AlphaComposite;
import java.awt.Graphics2D;
import java.awt.RenderingHints;
import java.awt.image.BufferedImage;

@Mod(BaritoneWebBridge.MOD_ID)
public final class BaritoneWebBridge {
    public static final String MOD_ID = "baritonewebbridge";
    private static final String VERSION = "2.5.3";
    private static final int FIRST_PORT = 8765;
    private static final int LAST_PORT = 8795;
    private static final int MAX_BODY_BYTES = 16 * 1024;
    private static final int MAX_CONFIG_BYTES = 128 * 1024;
    private static final Pattern COMMAND_FIELD = Pattern.compile("\\\"command\\\"\\s*:\\s*\\\"((?:\\\\.|[^\\\"\\\\])*)\\\"");
    private static final Pattern ACTION_FIELD = Pattern.compile("\\\"action\\\"\\s*:\\s*\\\"([a-z_]+)\\\"");
    private static final Pattern ITEM_ID = Pattern.compile("^[a-z0-9_.-]+:[a-z0-9_./-]+$");
    private static final Pattern ICON_KEY = Pattern.compile("^[0-9a-f]{64}$");
    private static final int ICON_RENDER_SIZE = 64;
    private static final String ICON_RENDER_SCHEMA = "minecraft-gui-fbo-v2";
    private static final long ICON_RENDER_FAILURE_TTL_MS = 60_000L;
    private static final Pattern MODEL_PARENT = Pattern.compile("\\\"parent\\\"\\s*:\\s*\\\"([^\\\"]+)\\\"");
    private static final Pattern MODEL_TEXTURES = Pattern.compile("\\\"textures\\\"\\s*:\\s*\\{(.*?)\\}", Pattern.DOTALL);
    private static final Pattern MODEL_TEXTURE_ENTRY = Pattern.compile("\\\"([^\\\"]+)\\\"\\s*:\\s*\\\"([^\\\"]+)\\\"");
    private static final Set<String> ALLOWED_ORIGINS = Set.of("null", "http://127.0.0.1", "http://localhost");
    private static final AtomicLong REQUEST_SEQUENCE = new AtomicLong();
    private static final AtomicBoolean COMMAND_PENDING = new AtomicBoolean();
    private static final long STARTED_AT = System.currentTimeMillis();
    private static final String INSTANCE_ID = UUID.randomUUID().toString();
    private static volatile String lastCommand = "";
    private static volatile String lastError = "";
    private static volatile long lastDurationMs;
    private Path gameDir;
    private Path webConfigFile;
    private List<Path> modJarPaths = List.of();
    private String iconAssetFingerprint = "";
    private Path iconDiskCacheDir;
    private Path catalogCacheFile;
    private final Map<String, Optional<byte[]>> itemIconCache = new ConcurrentHashMap<>();
    private final Map<String, byte[]> renderedIconCache = Collections.synchronizedMap(new LinkedHashMap<>(256, 0.75f, true) {
        @Override protected boolean removeEldestEntry(Map.Entry<String, byte[]> eldest) { return size() > 512; }
    });
    private final Map<String, Object> iconStackCache = Collections.synchronizedMap(new LinkedHashMap<>(512, 0.75f, true) {
        @Override protected boolean removeEldestEntry(Map.Entry<String, Object> eldest) { return size() > 2048; }
    });
    private final Map<String, String> iconIdByKey = Collections.synchronizedMap(new LinkedHashMap<>(512, 0.75f, true) {
        @Override protected boolean removeEldestEntry(Map.Entry<String, String> eldest) { return size() > 2048; }
    });
    private final Map<String, CompletableFuture<byte[]>> iconRenderPending = new ConcurrentHashMap<>();
    private final Map<String, Long> iconRenderFailureUntil = new ConcurrentHashMap<>();
    private final Map<String, List<Path>> namespaceJarCache = new ConcurrentHashMap<>();
    private HttpServer server;
    private int port = -1;
    private ExecutorService commandExecutor;
    private ScheduledExecutorService quotaExecutor;
    private volatile QuotaSession quotaSession;

    public BaritoneWebBridge() {
        // Forge loads one-sided mods on both physical sides; on a dedicated server this bridge must do nothing.
        if (!Mc.isClientEnvironment()) return;
        gameDir = Path.of(System.getProperty("user.dir", ".")).toAbsolutePath().normalize();
        DebugLog.start(gameDir.resolve("logs").resolve("baritone-web-bridge.log"));
        webConfigFile = gameDir.resolve("config").resolve("baritone-web-bridge-settings.json");
        modJarPaths = scanModJars(gameDir.resolve("mods"));
        iconAssetFingerprint = computeAssetFingerprint(gameDir, modJarPaths);
        iconDiskCacheDir = gameDir.resolve("cache").resolve("baritone-web-bridge").resolve("item-icons")
                .resolve(iconAssetFingerprint.substring(0, 16));
        catalogCacheFile = gameDir.resolve("cache").resolve("baritone-web-bridge").resolve("catalog-" + iconAssetFingerprint.substring(0, 16) + ".json");
        try { Files.createDirectories(iconDiskCacheDir); }
        catch (IOException error) { DebugLog.error("ITEM-ICON", "Could not create rendered icon cache directory", error); }
        DebugLog.info("ITEM-ICON", "Rendered icon cache=" + iconDiskCacheDir + ", fingerprint=" + iconAssetFingerprint.substring(0, 16));
        DebugLog.info("BOOT", "Starting Baritone Web Bridge " + VERSION);
        DebugLog.info("BOOT", "Java=" + System.getProperty("java.version") + ", OS=" + System.getProperty("os.name") + " " + System.getProperty("os.version"));
        DebugLog.info("BOOT", "Minecraft=" + modVersion("minecraft") + ", Forge=" + modVersion("forge") + ", Baritone=" + modVersion("baritone"));
        DebugLog.info("BOOT", "Game directory=" + gameDir);
        try {
            server = createServer();
            server.createContext("/api/status", this::handleStatus);
            server.createContext("/api/command", this::handleCommand);
            server.createContext("/api/inventory", this::handleInventory);
            server.createContext("/api/inventory/action", this::handleInventoryAction);
            server.createContext("/api/item-icon", this::handleItemIcon);
            server.createContext("/api/catalog", this::handleCatalog);
            server.createContext("/api/cache", this::handleCache);
            server.createContext("/api/cache/open", this::handleCacheOpen);
            server.createContext("/api/cache/clear", this::handleCacheClear);
            server.createContext("/api/settings", this::handleSettings);
            server.createContext("/api/web-config", this::handleWebConfig);
            server.setExecutor(Executors.newFixedThreadPool(3, runnable -> {
                Thread thread = new Thread(runnable, "baritone-web-http");
                thread.setDaemon(true);
                thread.setUncaughtExceptionHandler((ignored, error) -> DebugLog.error("HTTP", "Uncaught HTTP worker error", error));
                return thread;
            }));
            commandExecutor = Executors.newSingleThreadExecutor(runnable -> {
                Thread thread = new Thread(runnable, "baritone-web-command");
                thread.setDaemon(true);
                thread.setUncaughtExceptionHandler((ignored, error) -> DebugLog.error("COMMAND", "Uncaught command worker error", error));
                return thread;
            });
            quotaExecutor = Executors.newSingleThreadScheduledExecutor(runnable -> {
                Thread thread = new Thread(runnable, "baritone-web-quota");
                thread.setDaemon(true);
                return thread;
            });
            quotaExecutor.scheduleAtFixedRate(() -> {
                try { Mc.execute(this::checkQuotaProgress); }
                catch (Throwable ignored) { }
            }, 500, 500, TimeUnit.MILLISECONDS);
            server.start();
            Runtime.getRuntime().addShutdownHook(new Thread(this::shutdown, "baritone-web-shutdown"));
            DebugLog.info("BOOT", "Instance=" + INSTANCE_ID + ", listening on http://127.0.0.1:" + port);
            System.out.println("[Baritone Web Bridge] Listening on http://127.0.0.1:" + port + " | log: logs/baritone-web-bridge.log");
        } catch (Throwable error) {
            lastError = rootMessage(error);
            DebugLog.error("BOOT", "Could not start HTTP server", error);
            System.err.println("[Baritone Web Bridge] Could not start: " + lastError);
        }
    }

    private HttpServer createServer() throws IOException {
        IOException last = null;
        for (int candidate = FIRST_PORT; candidate <= LAST_PORT; candidate++) {
            try {
                HttpServer created = HttpServer.create(new InetSocketAddress("127.0.0.1", candidate), 0);
                port = candidate;
                return created;
            } catch (IOException error) {
                last = error;
                DebugLog.info("BOOT", "Port " + candidate + " is busy, trying the next one");
            }
        }
        throw new IOException("No free bridge port in range " + FIRST_PORT + "-" + LAST_PORT, last);
    }

    private void shutdown() {
        DebugLog.info("STOP", "Stopping bridge");
        if (server != null) server.stop(0);
        if (commandExecutor != null) commandExecutor.shutdownNow();
        if (quotaExecutor != null) quotaExecutor.shutdownNow();
        DebugLog.stop();
    }

    private void handleStatus(HttpExchange exchange) throws IOException {
        long requestId = REQUEST_SEQUENCE.incrementAndGet();
        if (!prepare(exchange, "GET", requestId)) return;
        Object player = Mc.player();
        boolean baritone = isBaritoneAvailable();
        boolean inGame = player != null && Mc.level() != null;
        String playerName = player != null ? Mc.playerName(player) : Mc.sessionUserName();
        String json = "{\"online\":true,\"baritone\":" + baritone + ",\"inGame\":" + inGame
                + ",\"pending\":" + COMMAND_PENDING.get() + ",\"version\":\"" + VERSION + "\",\"requestId\":" + requestId
                + ",\"instanceId\":\"" + INSTANCE_ID + "\",\"port\":" + port + ",\"playerName\":\"" + jsonEscape(playerName) + "\""
                + ",\"lastCommand\":\"" + jsonEscape(lastCommand) + "\",\"lastError\":\"" + jsonEscape(lastError)
                + "\",\"lastDurationMs\":" + lastDurationMs + ",\"uptimeMs\":" + (System.currentTimeMillis() - STARTED_AT) + "}";
        respond(exchange, 200, json, requestId);
    }

    private void handleInventory(HttpExchange exchange) throws IOException {
        long requestId = REQUEST_SEQUENCE.incrementAndGet();
        if (!prepare(exchange, "GET", requestId)) return;
        CompletableFuture<String> inventory = new CompletableFuture<>();
        try {
            Mc.execute(() -> {
                try { inventory.complete(buildInventoryJson(requestId)); }
                catch (Throwable error) { inventory.completeExceptionally(error); }
            });
        } catch (Throwable error) {
            fail(exchange, 503, "Minecraft client is not ready: " + rootMessage(error), requestId);
            return;
        }
        try {
            respond(exchange, 200, inventory.get(2, TimeUnit.SECONDS), requestId);
        } catch (Exception error) {
            fail(exchange, 503, "Could not read inventory: " + rootMessage(error), requestId);
        }
    }

    private void handleItemIcon(HttpExchange exchange) throws IOException {
        long requestId = REQUEST_SEQUENCE.incrementAndGet();
        if (!prepare(exchange, "GET", requestId)) return;
        String iconKey = queryParameter(exchange, "key");
        String itemId = queryParameter(exchange, "id");
        if (iconKey != null && !iconKey.isBlank() && !ICON_KEY.matcher(iconKey).matches()) {
            fail(exchange, 400, "Invalid icon key", requestId);
            return;
        }
        if (itemId != null && !itemId.isBlank() && !ITEM_ID.matcher(itemId).matches()) {
            fail(exchange, 400, "Invalid item id", requestId);
            return;
        }
        if ((iconKey == null || iconKey.isBlank()) && (itemId == null || itemId.isBlank())) {
            fail(exchange, 400, "Missing icon key or item id", requestId);
            return;
        }

        byte[] png = null;
        if (iconKey != null && !iconKey.isBlank()) {
            try { png = renderedIcon(iconKey, itemId, requestId); }
            catch (Throwable error) { DebugLog.error(requestId, "ITEM-RENDER", "Rendered icon failed for " + iconKey, error); }
        }
        if (png == null && itemId != null && !itemId.isBlank()) png = resourceIcon(itemId, requestId);
        if (png == null) {
            fail(exchange, 404, "No icon could be rendered" + (itemId == null ? "" : " for " + itemId), requestId);
            return;
        }
        respondBytes(exchange, 200, "image/png", png, requestId, "public, max-age=86400, immutable");
    }

    private void handleCache(HttpExchange exchange) throws IOException {
        long requestId = REQUEST_SEQUENCE.incrementAndGet();
        if (!prepare(exchange, "GET", requestId)) return;
        respond(exchange, 200, "{\"ok\":true,\"path\":\"" + jsonEscape(iconDiskCacheDir.toAbsolutePath().toString())
                + "\",\"bytes\":" + cacheSize(iconDiskCacheDir) + "}", requestId);
    }

    private void handleCatalog(HttpExchange exchange) throws IOException {
        long requestId = REQUEST_SEQUENCE.incrementAndGet();
        if (!prepare(exchange, "GET", requestId)) return;
        try {
            String json;
            if (Files.isRegularFile(catalogCacheFile)) json = Files.readString(catalogCacheFile, StandardCharsets.UTF_8);
            else {
                json = buildCatalogJson();
                Files.createDirectories(catalogCacheFile.getParent());
                Files.writeString(catalogCacheFile, json, StandardCharsets.UTF_8, StandardOpenOption.CREATE, StandardOpenOption.TRUNCATE_EXISTING);
            }
            respond(exchange, 200, json, requestId);
        } catch (Throwable error) { fail(exchange, 503, "Could not build registry catalog: " + rootMessage(error), requestId); }
    }

    private String buildCatalogJson() throws Exception {
        Class<?> registries = Class.forName("net.minecraftforge.registries.ForgeRegistries");
        Object blocks = registries.getField("BLOCKS").get(null);
        Object items = registries.getField("ITEMS").get(null);
        Method getKeys = Class.forName("net.minecraftforge.registries.IForgeRegistry").getMethod("getKeys");
        @SuppressWarnings("unchecked") Set<Object> blockKeys = (Set<Object>) getKeys.invoke(blocks);
        @SuppressWarnings("unchecked") Set<Object> itemKeys = (Set<Object>) getKeys.invoke(items);
        List<String> blockIds = blockKeys.stream().map(String::valueOf).sorted().toList();
        Set<String> blockSet = Set.copyOf(blockIds);
        List<String> itemIds = itemKeys.stream().map(String::valueOf).filter(id -> !blockSet.contains(id)).sorted().toList();
        return "{\"ok\":true,\"fingerprint\":\"" + iconAssetFingerprint.substring(0, 16) + "\",\"blocks\":["
                + blockIds.stream().map(id -> "\"" + jsonEscape(id) + "\"").collect(java.util.stream.Collectors.joining(","))
                + "],\"items\":[" + itemIds.stream().map(id -> "\"" + jsonEscape(id) + "\"").collect(java.util.stream.Collectors.joining(",")) + "]}";
    }

    private void handleCacheOpen(HttpExchange exchange) throws IOException {
        long requestId = REQUEST_SEQUENCE.incrementAndGet();
        if (!prepare(exchange, "POST", requestId)) return;
        try {
            new ProcessBuilder("explorer.exe", iconDiskCacheDir.toAbsolutePath().toString()).start();
            respond(exchange, 200, "{\"ok\":true}", requestId);
        } catch (IOException error) { fail(exchange, 503, "Could not open cache folder", requestId); }
    }

    private void handleCacheClear(HttpExchange exchange) throws IOException {
        long requestId = REQUEST_SEQUENCE.incrementAndGet();
        if (!prepare(exchange, "POST", requestId)) return;
        long removed = 0;
        try (var files = Files.walk(iconDiskCacheDir)) {
            for (Path path : files.filter(Files::isRegularFile).toList()) { Files.deleteIfExists(path); removed++; }
            renderedIconCache.clear(); itemIconCache.clear();
            respond(exchange, 200, "{\"ok\":true,\"removed\":" + removed + "}", requestId);
        } catch (IOException error) { fail(exchange, 503, "Could not clear cache: " + rootMessage(error), requestId); }
    }

    private static long cacheSize(Path directory) {
        if (directory == null || !Files.isDirectory(directory)) return 0;
        try (var files = Files.walk(directory)) { return files.filter(Files::isRegularFile).mapToLong(path -> { try { return Files.size(path); } catch (IOException ignored) { return 0; } }).sum(); }
        catch (IOException ignored) { return 0; }
    }

    private byte[] renderedIcon(String iconKey, String requestedItemId, long requestId) throws Exception {
        byte[] memory = renderedIconCache.get(iconKey);
        if (memory != null) return memory;

        Path disk = iconDiskCacheDir == null ? null : iconDiskCacheDir.resolve(iconKey + ".png");
        if (disk != null && Files.isRegularFile(disk)) {
            try {
                byte[] bytes = Files.readAllBytes(disk);
                if (bytes.length > 32) {
                    renderedIconCache.put(iconKey, bytes);
                    return bytes;
                }
            } catch (IOException error) {
                DebugLog.info(requestId, "ITEM-RENDER", "Ignoring unreadable disk cache " + disk.getFileName() + ": " + error.getMessage());
            }
        }

        Object stack = iconStackCache.get(iconKey);
        String itemId = iconIdByKey.get(iconKey);
        if (itemId == null) itemId = requestedItemId;
        Long failedUntil = iconRenderFailureUntil.get(iconKey);
        if (failedUntil != null) {
            if (failedUntil > System.currentTimeMillis()) {
                DebugLog.info(requestId, "ITEM-RENDER", "Skipping recent failed render for "
                        + (itemId == null ? iconKey.substring(0, 12) : itemId));
                return itemId == null ? null : resourceIcon(itemId, requestId);
            }
            iconRenderFailureUntil.remove(iconKey, failedUntil);
        }
        if (stack == null) {
            DebugLog.info(requestId, "ITEM-RENDER", "No ItemStack snapshot for key " + iconKey.substring(0, 12) + "; using resource fallback");
            return itemId == null ? null : resourceIcon(itemId, requestId);
        }

        final Object stackSnapshot = stack;
        final String fallbackId = itemId;
        CompletableFuture<byte[]> created = new CompletableFuture<>();
        CompletableFuture<byte[]> future = iconRenderPending.putIfAbsent(iconKey, created);
        if (future == null) {
            future = created;
            try {
                Mc.execute(() -> {
                    try {
                        long started = System.nanoTime();
                        byte[] bytes = Mc.renderItemStackIconPng(stackSnapshot, ICON_RENDER_SIZE);
                        if (bytes == null || bytes.length == 0) throw new IllegalStateException("Minecraft renderer returned an empty image");
                        renderedIconCache.put(iconKey, bytes);
                        iconRenderFailureUntil.remove(iconKey);
                        DebugLog.info(requestId, "ITEM-RENDER", "Rendered " + (fallbackId == null ? iconKey.substring(0, 12) : fallbackId)
                                + " through Minecraft in " + elapsedMs(started) + " ms (" + bytes.length + " bytes)");
                        created.complete(bytes);
                    } catch (Throwable error) {
                        iconRenderFailureUntil.put(iconKey, System.currentTimeMillis() + ICON_RENDER_FAILURE_TTL_MS);
                        DebugLog.error(requestId, "ITEM-RENDER", "Minecraft item render failed for " + (fallbackId == null ? iconKey : fallbackId), error);
                        created.completeExceptionally(error);
                    } finally {
                        iconRenderPending.remove(iconKey, created);
                    }
                });
            } catch (Throwable error) {
                iconRenderPending.remove(iconKey, created);
                created.completeExceptionally(error);
            }
        }

        try {
            byte[] bytes = future.get(5, TimeUnit.SECONDS);
            if (disk != null && bytes != null && bytes.length > 0 && !Files.exists(disk)) {
                try {
                    Files.createDirectories(disk.getParent());
                    Files.write(disk, bytes, StandardOpenOption.CREATE, StandardOpenOption.TRUNCATE_EXISTING);
                } catch (IOException error) {
                    DebugLog.info(requestId, "ITEM-RENDER", "Could not persist rendered icon: " + error.getMessage());
                }
            }
            return bytes;
        } catch (Exception renderError) {
            if (fallbackId != null) {
                byte[] fallback = resourceIcon(fallbackId, requestId);
                if (fallback != null) return fallback;
            }
            throw renderError;
        }
    }

    private byte[] resourceIcon(String itemId, long requestId) {
        Optional<byte[]> cached = itemIconCache.computeIfAbsent(itemId, id -> {
            try { return Optional.ofNullable(resolveItemIcon(id)); }
            catch (Throwable error) {
                DebugLog.error(requestId, "ITEM-ICON", "Could not resolve resource icon " + id, error);
                return Optional.empty();
            }
        });
        return cached.orElse(null);
    }

    private static String computeAssetFingerprint(Path gameDir, List<Path> jars) {
        try {
            MessageDigest digest = MessageDigest.getInstance("SHA-256");
            digest.update((ICON_RENDER_SCHEMA + "|" + VERSION + "\n").getBytes(StandardCharsets.UTF_8));
            for (Path jar : jars) {
                try {
                    digest.update((jar.getFileName() + "|" + Files.size(jar) + "|" + Files.getLastModifiedTime(jar).toMillis() + "\n")
                            .getBytes(StandardCharsets.UTF_8));
                } catch (IOException ignored) { digest.update((jar.getFileName() + "\n").getBytes(StandardCharsets.UTF_8)); }
            }
            Path options = gameDir.resolve("options.txt");
            if (Files.isRegularFile(options)) {
                try {
                    for (String line : Files.readAllLines(options, StandardCharsets.UTF_8)) {
                        if (line.startsWith("resourcePacks:") || line.startsWith("incompatibleResourcePacks:")) {
                            digest.update((line + "\n").getBytes(StandardCharsets.UTF_8));
                        }
                    }
                } catch (IOException ignored) { }
            }
            Path packs = gameDir.resolve("resourcepacks");
            if (Files.isDirectory(packs)) {
                try (var stream = Files.list(packs)) {
                    for (Path path : stream.sorted().toList()) {
                        try {
                            digest.update((path.getFileName() + "|" + Files.size(path) + "|" + Files.getLastModifiedTime(path).toMillis() + "\n")
                                    .getBytes(StandardCharsets.UTF_8));
                        } catch (IOException ignored) { digest.update((path.getFileName() + "\n").getBytes(StandardCharsets.UTF_8)); }
                    }
                } catch (IOException ignored) { }
            }
            return HexFormat.of().formatHex(digest.digest());
        } catch (Exception error) {
            return sha256Hex(ICON_RENDER_SCHEMA + "|" + VERSION + "|" + System.currentTimeMillis());
        }
    }

    private static String sha256Hex(String value) {
        try {
            MessageDigest digest = MessageDigest.getInstance("SHA-256");
            return HexFormat.of().formatHex(digest.digest(value.getBytes(StandardCharsets.UTF_8)));
        } catch (Exception error) {
            throw new IllegalStateException("SHA-256 is unavailable", error);
        }
    }

    private static String queryParameter(HttpExchange exchange, String wanted) {
        String query = exchange.getRequestURI().getRawQuery();
        if (query == null || query.isEmpty()) return null;
        for (String pair : query.split("&")) {
            int eq = pair.indexOf('=');
            String key = eq < 0 ? pair : pair.substring(0, eq);
            if (!wanted.equals(URLDecoder.decode(key, StandardCharsets.UTF_8))) continue;
            String value = eq < 0 ? "" : pair.substring(eq + 1);
            return URLDecoder.decode(value, StandardCharsets.UTF_8);
        }
        return null;
    }

    private static List<Path> scanModJars(Path modsDir) {
        if (!Files.isDirectory(modsDir)) return List.of();
        try (var stream = Files.list(modsDir)) {
            List<Path> jars = stream.filter(Files::isRegularFile)
                    .filter(path -> path.getFileName().toString().toLowerCase().endsWith(".jar"))
                    .sorted().toList();
            DebugLog.info("ITEM-ICON", "Indexed " + jars.size() + " mod jars for icon resources");
            return jars;
        } catch (IOException error) {
            DebugLog.error("ITEM-ICON", "Could not scan mods directory", error);
            return List.of();
        }
    }

    private byte[] resolveItemIcon(String itemId) throws IOException {
        int colon = itemId.indexOf(':');
        String namespace = itemId.substring(0, colon);
        String path = itemId.substring(colon + 1);

        // Fast path for the common case where the item has a directly named texture.
        for (String candidate : List.of(
                "assets/" + namespace + "/textures/item/" + path + ".png",
                "assets/" + namespace + "/textures/items/" + path + ".png")) {
            byte[] direct = readModResource(candidate);
            if (direct != null) return normalizeIconPng(direct);
        }

        ModelData model = loadModel(namespace + ":item/" + path, 0, new java.util.HashSet<>());

        // Some mods register blocks/items in code but do not ship a same-name item model. A flat
        // block texture/model is still much better than no icon at all.
        if (model == null || model.textures.isEmpty()) {
            for (String candidate : List.of(
                    "assets/" + namespace + "/textures/block/" + path + ".png",
                    "assets/" + namespace + "/textures/blocks/" + path + ".png")) {
                byte[] direct = readModResource(candidate);
                if (direct != null) return normalizeIconPng(direct);
            }
            ModelData blockModel = loadModel(namespace + ":block/" + path, 0, new java.util.HashSet<>());
            if (blockModel != null && !blockModel.textures.isEmpty()) model = blockModel;
        }

        // Spawn-egg models are frequently generated by Forge/datagen or inherit the vanilla
        // template. If the per-item model is absent, the vanilla template still gives us the two
        // correct egg layers; colors are applied below from SpawnEggItem itself.
        if ((model == null || model.textures.isEmpty()) && path.endsWith("_spawn_egg")) {
            model = loadModel("minecraft:item/template_spawn_egg", 0, new java.util.HashSet<>());
        }

        if (model == null || model.textures.isEmpty()) return null;

        List<String> layerRefs = new ArrayList<>();
        for (int layer = 0; layer < 16; layer++) {
            String value = model.textures.get("layer" + layer);
            if (value == null) break;
            String resolved = resolveTextureReference(value, model.textures, namespace, 0);
            if (resolved != null) layerRefs.add(resolved);
        }
        if (!layerRefs.isEmpty()) {
            List<byte[]> layers = new ArrayList<>();
            for (int layer = 0; layer < layerRefs.size(); layer++) {
                byte[] png = readTextureReference(layerRefs.get(layer), namespace);
                if (png == null) continue;
                Integer tint = Mc.spawnEggColor(itemId, layer);
                if (tint != null) png = tintPng(png, tint);
                layers.add(png);
            }
            if (!layers.isEmpty()) return compositePngLayers(layers);
        }

        for (String key : List.of("particle", "all", "texture", "top", "side", "end", "north", "south", "east", "west", "up", "down")) {
            String value = model.textures.get(key);
            String resolved = resolveTextureReference(value, model.textures, namespace, 0);
            if (resolved == null) continue;
            byte[] png = readTextureReference(resolved, namespace);
            if (png != null) return normalizeIconPng(png);
        }
        for (String value : model.textures.values()) {
            String resolved = resolveTextureReference(value, model.textures, namespace, 0);
            if (resolved == null) continue;
            byte[] png = readTextureReference(resolved, namespace);
            if (png != null) return normalizeIconPng(png);
        }
        return null;
    }

    private ModelData loadModel(String modelRef, int depth, Set<String> visited) throws IOException {
        if (depth > 12 || modelRef == null || modelRef.isBlank()) return null;
        String normalized = modelRef.indexOf(':') >= 0 ? modelRef : "minecraft:" + modelRef;
        if (!visited.add(normalized)) return null;
        int colon = normalized.indexOf(':');
        String namespace = normalized.substring(0, colon);
        String path = normalized.substring(colon + 1);
        if (path.startsWith("builtin/") || path.equals("item/generated") || path.equals("item/handheld")) return new ModelData(namespace, new LinkedHashMap<>());
        byte[] bytes = readModResource("assets/" + namespace + "/models/" + path + ".json");
        if (bytes == null) return null;
        String json = new String(bytes, StandardCharsets.UTF_8);
        LinkedHashMap<String, String> textures = new LinkedHashMap<>();
        Matcher parentMatcher = MODEL_PARENT.matcher(json);
        if (parentMatcher.find()) {
            String parent = parentMatcher.group(1);
            if (parent.indexOf(':') < 0) parent = namespace + ":" + parent;
            ModelData parentData = loadModel(parent, depth + 1, visited);
            if (parentData != null) textures.putAll(parentData.textures);
        }
        Matcher block = MODEL_TEXTURES.matcher(json);
        if (block.find()) {
            Matcher entry = MODEL_TEXTURE_ENTRY.matcher(block.group(1));
            while (entry.find()) textures.put(entry.group(1), entry.group(2));
        }
        return new ModelData(namespace, textures);
    }

    private String resolveTextureReference(String value, Map<String, String> textures, String defaultNamespace, int depth) {
        if (value == null || value.isBlank() || depth > 16) return null;
        if (value.charAt(0) == '#') return resolveTextureReference(textures.get(value.substring(1)), textures, defaultNamespace, depth + 1);
        return value.indexOf(':') >= 0 ? value : defaultNamespace + ":" + value;
    }

    private byte[] readTextureReference(String ref, String defaultNamespace) throws IOException {
        String normalized = ref.indexOf(':') >= 0 ? ref : defaultNamespace + ":" + ref;
        int colon = normalized.indexOf(':');
        String namespace = normalized.substring(0, colon);
        String path = normalized.substring(colon + 1);
        return readModResource("assets/" + namespace + "/textures/" + path + ".png");
    }

    private byte[] readModResource(String entryName) throws IOException {
        // First ask Minecraft's active ResourceManager. Unlike scanning /mods directly this can
        // resolve vanilla parents such as minecraft:block/cube_all and
        // minecraft:item/template_spawn_egg, and it also respects resource-pack overrides.
        byte[] activeResource = Mc.readActiveResource(entryName);
        if (activeResource != null) return activeResource;

        // Keep the direct JAR scan as a compatibility fallback for unusual packs/load timing.
        for (Path jarPath : jarsForResource(entryName)) {
            try (JarFile jar = new JarFile(jarPath.toFile())) {
                JarEntry entry = jar.getJarEntry(entryName);
                if (entry == null || entry.isDirectory()) continue;
                try (var input = jar.getInputStream(entry)) { return input.readAllBytes(); }
            } catch (IOException error) {
                DebugLog.info("ITEM-ICON", "Skipping unreadable jar " + jarPath.getFileName() + ": " + error.getMessage());
            }
        }
        return null;
    }

    private List<Path> jarsForResource(String entryName) {
        String prefix = "assets/";
        if (!entryName.startsWith(prefix)) return modJarPaths;
        int slash = entryName.indexOf('/', prefix.length());
        if (slash < 0) return modJarPaths;
        String namespace = entryName.substring(prefix.length(), slash);
        return namespaceJarCache.computeIfAbsent(namespace, ns -> {
            String namespacePrefix = "assets/" + ns + "/";
            List<Path> matches = new ArrayList<>();
            for (Path jarPath : modJarPaths) {
                try (JarFile jar = new JarFile(jarPath.toFile())) {
                    boolean found = jar.stream().anyMatch(entry -> entry.getName().startsWith(namespacePrefix));
                    if (found) matches.add(jarPath);
                } catch (IOException error) {
                    DebugLog.info("ITEM-ICON", "Skipping unreadable jar " + jarPath.getFileName() + ": " + error.getMessage());
                }
            }
            DebugLog.info("ITEM-ICON", "Namespace " + ns + " is provided by " + matches.size() + " mod jar(s)");
            return List.copyOf(matches);
        });
    }

    private static byte[] normalizeIconPng(byte[] png) throws IOException {
        BufferedImage source = ImageIO.read(new ByteArrayInputStream(png));
        if (source == null) return png;
        int frame = Math.min(source.getWidth(), source.getHeight());
        BufferedImage normalized = new BufferedImage(frame, frame, BufferedImage.TYPE_INT_ARGB);
        Graphics2D graphics = normalized.createGraphics();
        try {
            graphics.setComposite(AlphaComposite.Src);
            graphics.setRenderingHint(RenderingHints.KEY_INTERPOLATION, RenderingHints.VALUE_INTERPOLATION_NEAREST_NEIGHBOR);
            graphics.drawImage(source, 0, 0, frame, frame, 0, 0, frame, frame, null);
        } finally { graphics.dispose(); }
        ByteArrayOutputStream output = new ByteArrayOutputStream();
        ImageIO.write(normalized, "PNG", output);
        return output.toByteArray();
    }

    private static byte[] tintPng(byte[] png, int rgb) throws IOException {
        BufferedImage source = ImageIO.read(new ByteArrayInputStream(png));
        if (source == null) return png;
        BufferedImage tinted = new BufferedImage(source.getWidth(), source.getHeight(), BufferedImage.TYPE_INT_ARGB);
        int tr = (rgb >> 16) & 0xff;
        int tg = (rgb >> 8) & 0xff;
        int tb = rgb & 0xff;
        for (int y = 0; y < source.getHeight(); y++) {
            for (int x = 0; x < source.getWidth(); x++) {
                int argb = source.getRGB(x, y);
                int a = (argb >>> 24) & 0xff;
                int r = (argb >>> 16) & 0xff;
                int g = (argb >>> 8) & 0xff;
                int b = argb & 0xff;
                int nr = r * tr / 255;
                int ng = g * tg / 255;
                int nb = b * tb / 255;
                tinted.setRGB(x, y, (a << 24) | (nr << 16) | (ng << 8) | nb);
            }
        }
        ByteArrayOutputStream output = new ByteArrayOutputStream();
        ImageIO.write(tinted, "PNG", output);
        return output.toByteArray();
    }

    private static byte[] compositePngLayers(List<byte[]> pngLayers) throws IOException {
        List<BufferedImage> images = new ArrayList<>();
        int size = 0;
        for (byte[] bytes : pngLayers) {
            BufferedImage source = ImageIO.read(new ByteArrayInputStream(bytes));
            if (source == null) continue;
            int frame = Math.min(source.getWidth(), source.getHeight());
            size = Math.max(size, frame);
            images.add(source.getSubimage(0, 0, frame, frame));
        }
        if (images.isEmpty()) return null;
        BufferedImage result = new BufferedImage(size, size, BufferedImage.TYPE_INT_ARGB);
        Graphics2D graphics = result.createGraphics();
        try {
            graphics.setRenderingHint(RenderingHints.KEY_INTERPOLATION, RenderingHints.VALUE_INTERPOLATION_NEAREST_NEIGHBOR);
            for (BufferedImage image : images) graphics.drawImage(image, 0, 0, size, size, null);
        } finally { graphics.dispose(); }
        ByteArrayOutputStream output = new ByteArrayOutputStream();
        ImageIO.write(result, "PNG", output);
        return output.toByteArray();
    }

    private record ModelData(String namespace, Map<String, String> textures) {}

    private void handleInventoryAction(HttpExchange exchange) throws IOException {
        long requestId = REQUEST_SEQUENCE.incrementAndGet();
        if (!prepare(exchange, "POST", requestId)) return;
        byte[] bytes = exchange.getRequestBody().readNBytes(MAX_BODY_BYTES + 1);
        if (bytes.length > MAX_BODY_BYTES) { fail(exchange, 413, "Request is too large", requestId); return; }
        String body = new String(bytes, StandardCharsets.UTF_8);
        String action = readStringField(body, ACTION_FIELD);
        if (action == null) { fail(exchange, 400, "Missing inventory action", requestId); return; }
        int fromSlot = readIntField(body, "fromSlot", -1);
        int toSlot = readIntField(body, "toSlot", -1);
        int hotbarSlot = readIntField(body, "hotbarSlot", -1);
        CompletableFuture<String> result = new CompletableFuture<>();
        try {
            Mc.execute(() -> {
                try { result.complete(performInventoryAction(action, fromSlot, toSlot, hotbarSlot, requestId)); }
                catch (Throwable error) { result.completeExceptionally(error); }
            });
        } catch (Throwable error) {
            fail(exchange, 503, "Minecraft client is not ready: " + rootMessage(error), requestId);
            return;
        }
        try {
            respond(exchange, 200, result.get(2, TimeUnit.SECONDS), requestId);
        } catch (Exception error) {
            fail(exchange, 503, "Inventory action failed: " + rootMessage(error), requestId);
        }
    }

    private String performInventoryAction(String action, int fromSlot, int toSlot, int hotbarSlot, long requestId) {
        Object player = Mc.player();
        Object level = Mc.level();
        Object gameMode = Mc.gameMode();
        if (player == null || level == null || gameMode == null) {
            throw new IllegalStateException("Open a world or join a server first");
        }
        Object handler = Mc.containerMenu(player);
        validateHandlerSlot(handler, fromSlot, "fromSlot");
        switch (action) {
            case "move" -> {
                validateHandlerSlot(handler, toSlot, "toSlot");
                if (fromSlot == toSlot) throw new IllegalArgumentException("Source and target slots are equal");
                Mc.clickSlot(gameMode, handler, fromSlot, 0, "PICKUP", player);
                Mc.clickSlot(gameMode, handler, toSlot, 0, "PICKUP", player);
                if (!Mc.itemStackEmpty(Mc.carried(handler))) {
                    Mc.clickSlot(gameMode, handler, fromSlot, 0, "PICKUP", player);
                }
            }
            case "quick_move" -> Mc.clickSlot(gameMode, handler, fromSlot, 0, "QUICK_MOVE", player);
            case "drop_one" -> Mc.clickSlot(gameMode, handler, fromSlot, 0, "THROW", player);
            case "drop_stack" -> Mc.clickSlot(gameMode, handler, fromSlot, 1, "THROW", player);
            case "swap_hotbar" -> {
                if (hotbarSlot < 0 || hotbarSlot > 8) throw new IllegalArgumentException("hotbarSlot must be between 0 and 8");
                Mc.clickSlot(gameMode, handler, fromSlot, hotbarSlot, "SWAP", player);
            }
            default -> throw new IllegalArgumentException("Unsupported inventory action: " + action);
        }
        int syncId = Mc.containerId(handler);
        DebugLog.info(requestId, "INVENTORY-ACTION", action + " from=" + fromSlot + " to=" + toSlot + " hotbar=" + hotbarSlot + " syncId=" + syncId);
        return "{\"ok\":true,\"requestId\":" + requestId + ",\"action\":\"" + jsonEscape(action) + "\"}";
    }

    private static void validateHandlerSlot(Object handler, int slot, String field) {
        if (slot < 0 || slot >= Mc.slots(handler).size()) throw new IllegalArgumentException(field + " is outside the current screen handler");
    }

    private void handleSettings(HttpExchange exchange) throws IOException {
        long requestId = REQUEST_SEQUENCE.incrementAndGet();
        if (!prepare(exchange, "GET", requestId)) return;
        try {
            Class<?> apiClass = Class.forName("baritone.api.BaritoneAPI");
            Object settings = apiClass.getMethod("getSettings").invoke(null);
            Object allSettings = settings.getClass().getField("allSettings").get(settings);
            StringBuilder json = new StringBuilder("{\"ok\":true,\"instanceId\":\"").append(INSTANCE_ID).append("\",\"settings\":{");
            boolean first = true;
            for (Object setting : (Iterable<?>) allSettings) {
                boolean javaOnly = (boolean) setting.getClass().getMethod("isJavaOnly").invoke(setting);
                if (javaOnly) continue;
                String name = (String) setting.getClass().getMethod("getName").invoke(setting);
                String value = setting.toString();
                if (!first) json.append(',');
                first = false;
                json.append('\"').append(jsonEscape(name)).append("\":\"").append(jsonEscape(value)).append('\"');
            }
            json.append("},\"configPath\":\"").append(jsonEscape(webConfigFile.toAbsolutePath().toString())).append("\"}");
            DebugLog.info(requestId, "SETTINGS", "Returned live Baritone settings");
            respond(exchange, 200, json.toString(), requestId);
        } catch (Throwable error) {
            fail(exchange, 503, "Could not read Baritone settings: " + rootMessage(error), requestId);
        }
    }

    private void handleWebConfig(HttpExchange exchange) throws IOException {
        long requestId = REQUEST_SEQUENCE.incrementAndGet();
        String method = exchange.getRequestMethod();
        if ("GET".equals(method)) {
            if (!prepare(exchange, "GET", requestId)) return;
            String config = Files.exists(webConfigFile) ? Files.readString(webConfigFile, StandardCharsets.UTF_8) : "{\"version\":1,\"settings\":{}}";
            respond(exchange, 200, "{\"ok\":true,\"configPath\":\"" + jsonEscape(webConfigFile.toAbsolutePath().toString()) + "\",\"config\":" + config + "}", requestId);
            return;
        }
        if ("POST".equals(method)) {
            if (!prepare(exchange, "POST", requestId)) return;
            byte[] body = exchange.getRequestBody().readNBytes(MAX_CONFIG_BYTES + 1);
            if (body.length > MAX_CONFIG_BYTES) { fail(exchange, 413, "Config is too large", requestId); return; }
            String config = new String(body, StandardCharsets.UTF_8).trim();
            if (!config.startsWith("{") || !config.endsWith("}")) { fail(exchange, 400, "Config must be a JSON object", requestId); return; }
            Files.createDirectories(webConfigFile.getParent());
            Files.writeString(webConfigFile, config + System.lineSeparator(), StandardCharsets.UTF_8, StandardOpenOption.CREATE, StandardOpenOption.TRUNCATE_EXISTING);
            DebugLog.info(requestId, "CONFIG", "Saved web config to " + webConfigFile.toAbsolutePath());
            respond(exchange, 200, "{\"ok\":true,\"configPath\":\"" + jsonEscape(webConfigFile.toAbsolutePath().toString()) + "\"}", requestId);
            return;
        }
        addCors(exchange);
        fail(exchange, 405, "Method not allowed", requestId);
    }

    private String registerIconStack(Object stack, String itemId) {
        String renderIdentity;
        try { renderIdentity = Mc.stackRenderIdentity(stack); }
        catch (Throwable error) { renderIdentity = "damage=" + Mc.itemDamage(stack); }
        String iconKey = sha256Hex(ICON_RENDER_SCHEMA + "|" + iconAssetFingerprint + "|" + itemId + "|" + renderIdentity);
        try { iconStackCache.put(iconKey, Mc.copyStack(stack)); }
        catch (Throwable error) { iconStackCache.put(iconKey, stack); }
        iconIdByKey.put(iconKey, itemId);
        return iconKey;
    }

    private String buildInventoryJson(long requestId) {
        Object player = Mc.player();
        if (player == null || Mc.level() == null) throw new IllegalStateException("Open a world or join a server first");
        Object handler = Mc.containerMenu(player);
        Object inventory = Mc.inventory(player);
        StringBuilder slots = new StringBuilder();
        int size = Mc.inventorySize(inventory);
        for (int slot = 0; slot < size; slot++) {
            Object stack = Mc.inventoryItem(inventory, slot);
            if (slot > 0) slots.append(',');
            String section = slot < 9 ? "hotbar" : slot < 36 ? "main" : slot < 40 ? "armor" : "offhand";
            slots.append("{\"slot\":").append(slot).append(",\"handlerSlot\":").append(findHandlerSlot(handler, inventory, slot))
                    .append(",\"section\":\"").append(section).append("\"");
            if (!Mc.itemStackEmpty(stack)) {
                String itemId = Mc.itemId(stack);
                String iconKey = registerIconStack(stack, itemId);
                slots.append(",\"id\":\"").append(jsonEscape(itemId)).append("\",\"iconKey\":\"").append(iconKey)
                        .append("\",\"name\":\"").append(jsonEscape(Mc.itemName(stack))).append("\",\"count\":").append(Mc.itemCount(stack))
                        .append(",\"damage\":").append(Mc.itemDamage(stack)).append(",\"maxDamage\":").append(Mc.itemMaxDamage(stack));
            }
            slots.append('}');
        }
        StringBuilder containerSlots = new StringBuilder();
        int containerIndex = 0;
        List<?> handlerSlots = Mc.slots(handler);
        for (int handlerSlot = 0; handlerSlot < handlerSlots.size(); handlerSlot++) {
            Object slot = handlerSlots.get(handlerSlot);
            if (Mc.slotContainer(slot) == inventory) continue;
            if (containerIndex++ > 0) containerSlots.append(',');
            Object stack = Mc.slotItem(slot);
            containerSlots.append("{\"slot\":").append(containerIndex - 1).append(",\"handlerSlot\":").append(handlerSlot);
            if (!Mc.itemStackEmpty(stack)) {
                String itemId = Mc.itemId(stack);
                String iconKey = registerIconStack(stack, itemId);
                containerSlots.append(",\"id\":\"").append(jsonEscape(itemId)).append("\",\"iconKey\":\"").append(iconKey)
                        .append("\",\"name\":\"").append(jsonEscape(Mc.itemName(stack))).append("\",\"count\":").append(Mc.itemCount(stack))
                        .append(",\"damage\":").append(Mc.itemDamage(stack)).append(",\"maxDamage\":").append(Mc.itemMaxDamage(stack));
            }
            containerSlots.append('}');
        }
        boolean containerOpen = handler != Mc.inventoryMenu(player) && containerIndex > 0;
        String containerTitle = containerOpen ? Mc.currentScreenTitle() : "";
        String playerName = Mc.playerName(player);
        float health = Mc.floatValue(player, new String[]{"m_21223_", "getHealth"});
        float maxHealth = Mc.floatValue(player, new String[]{"m_21233_", "getMaxHealth"});
        Object foodData = Mc.invokeNoArgs(player, "m_36324_", "getFoodData");
        int food = Mc.intValue(foodData, new String[]{"m_38702_", "getFoodLevel"});
        float saturation = Mc.floatValue(foodData, new String[]{"m_38722_", "getSaturationLevel"});
        int armor = Mc.intValue(player, new String[]{"m_21230_", "getArmorValue"});
        int experienceLevel = ((Number) Mc.field(player, "f_36078_", "experienceLevel")).intValue();
        float experienceProgress = ((Number) Mc.field(player, "f_36080_", "experienceProgress")).floatValue();
        int syncId = Mc.containerId(handler);
        return "{\"ok\":true,\"instanceId\":\"" + INSTANCE_ID + "\",\"playerName\":\"" + jsonEscape(playerName)
                + "\",\"port\":" + port + ",\"health\":" + health + ",\"maxHealth\":" + maxHealth
                + ",\"food\":" + food + ",\"saturation\":" + saturation + ",\"armor\":" + armor
                + ",\"experienceLevel\":" + experienceLevel + ",\"experienceProgress\":" + experienceProgress
                + ",\"slots\":[" + slots + "],\"container\":" + (containerOpen
                ? "{\"title\":\"" + jsonEscape(containerTitle) + "\",\"syncId\":" + syncId + ",\"slots\":[" + containerSlots + "]}"
                : "null") + "}";
    }

    private int findHandlerSlot(Object handler, Object inventory, int inventorySlot) {
        List<?> slots = Mc.slots(handler);
        for (int index = 0; index < slots.size(); index++) {
            Object slot = slots.get(index);
            if (Mc.slotContainer(slot) == inventory && Mc.slotContainerIndex(slot) == inventorySlot) return index;
        }
        return -1;
    }

    private void handleCommand(HttpExchange exchange) throws IOException {
        long requestId = REQUEST_SEQUENCE.incrementAndGet();
        long receivedAt = System.nanoTime();
        if (!prepare(exchange, "POST", requestId)) return;
        String origin = exchange.getRequestHeaders().getFirst("Origin");
        DebugLog.info(requestId, "REQUEST", "POST /api/command origin=" + origin + " remote=" + exchange.getRemoteAddress());
        byte[] body = exchange.getRequestBody().readNBytes(MAX_BODY_BYTES + 1);
        DebugLog.info(requestId, "REQUEST", "Body bytes=" + body.length);
        if (body.length > MAX_BODY_BYTES) { fail(exchange, 413, "Request is too large", requestId); return; }
        String command = readCommand(new String(body, StandardCharsets.UTF_8));
        if (command == null || command.isBlank()) { fail(exchange, 400, "Missing command", requestId); return; }
        if (command.length() > 512 || command.indexOf('\n') >= 0 || command.indexOf('\r') >= 0) { fail(exchange, 400, "Invalid command", requestId); return; }
        if (!COMMAND_PENDING.compareAndSet(false, true)) { fail(exchange, 409, "Another command is still pending", requestId); return; }

        lastCommand = command;
        lastError = "";
        DebugLog.info(requestId, "QUEUE", "Command accepted: " + command);
        CompletableFuture<Boolean> result = new CompletableFuture<>();
        long queuedAt = System.nanoTime();
        commandExecutor.execute(() -> {
            long started = System.nanoTime();
            DebugLog.info(requestId, "COMMAND", "Command worker started after " + elapsedMs(queuedAt) + " ms; thread=" + Thread.currentThread().getName());
            try {
                warmBlockMetadata(command, requestId);
                CompletableFuture<Boolean> clientDispatch = new CompletableFuture<>();
                Mc.execute(() -> {
                    DebugLog.info(requestId, "CLIENT", "Baritone ChatEvent dispatch started on " + Thread.currentThread().getName());
                    try {
                        if (command.regionMatches(true, 0, "#minequota ", 0, 11)) clientDispatch.complete(startQuotaMining(command, requestId));
                        else {
                            if (command.equalsIgnoreCase("#cancel") || command.equalsIgnoreCase("#stop")) quotaSession = null;
                            clientDispatch.complete(dispatchThroughBaritoneEvent(command, requestId));
                        }
                    }
                    catch (Throwable error) { clientDispatch.completeExceptionally(error); }
                });
                boolean accepted = clientDispatch.get(8, TimeUnit.SECONDS);
                lastDurationMs = elapsedMs(started);
                DebugLog.info(requestId, "COMMAND", "Baritone returned " + accepted + " after " + lastDurationMs + " ms");
                result.complete(accepted);
            } catch (Throwable error) {
                lastDurationMs = elapsedMs(started);
                lastError = rootMessage(error);
                DebugLog.error(requestId, "COMMAND", "Command failed after " + lastDurationMs + " ms", error);
                result.completeExceptionally(error);
            } finally {
                COMMAND_PENDING.set(false);
            }
        });

        try {
            boolean accepted = result.get(8, TimeUnit.SECONDS);
            long totalMs = elapsedMs(receivedAt);
            if (accepted) {
                DebugLog.info(requestId, "RESPONSE", "200 OK total=" + totalMs + " ms");
                respond(exchange, 200, "{\"ok\":true,\"command\":\"" + jsonEscape(command) + "\",\"requestId\":" + requestId + ",\"durationMs\":" + totalMs + "}", requestId);
            } else {
                lastError = "Baritone rejected the command";
                fail(exchange, 422, lastError, requestId);
            }
        } catch (TimeoutException error) {
            String renderStack = DebugLog.renderThreadDump(requestId);
            lastError = "Baritone command timed out after 8 seconds" + (renderStack.isEmpty() ? "" : " | Render thread: " + renderStack);
            DebugLog.error(requestId, "TIMEOUT", lastError, error);
            fail(exchange, 504, lastError, requestId);
        } catch (Exception error) {
            lastError = rootMessage(error);
            DebugLog.error(requestId, "RESPONSE", "Command future failed", error);
            fail(exchange, 503, lastError, requestId);
        }
    }

    private boolean prepare(HttpExchange exchange, String method, long requestId) throws IOException {
        addCors(exchange);
        exchange.getResponseHeaders().set("X-Baritone-Bridge-Request-Id", Long.toString(requestId));
        if ("OPTIONS".equals(exchange.getRequestMethod())) { exchange.sendResponseHeaders(204, -1); exchange.close(); return false; }
        if (!method.equals(exchange.getRequestMethod())) { fail(exchange, 405, "Method not allowed", requestId); return false; }
        String origin = exchange.getRequestHeaders().getFirst("Origin");
        if (origin != null && !isAllowedOrigin(origin)) { fail(exchange, 403, "Origin not allowed", requestId); return false; }
        return true;
    }

    private void addCors(HttpExchange exchange) {
        String origin = exchange.getRequestHeaders().getFirst("Origin");
        if (origin == null || isAllowedOrigin(origin)) {
            Headers headers = exchange.getResponseHeaders();
            headers.set("Access-Control-Allow-Origin", origin == null ? "null" : origin);
            headers.set("Access-Control-Allow-Methods", "GET, POST, OPTIONS");
            headers.set("Access-Control-Allow-Headers", "Content-Type");
            headers.set("Access-Control-Expose-Headers", "X-Baritone-Bridge-Request-Id");
            headers.set("Access-Control-Max-Age", "600");
            headers.set("Vary", "Origin");
        }
    }

    private boolean isAllowedOrigin(String origin) {
        if (ALLOWED_ORIGINS.contains(origin)) return true;
        return origin.startsWith("http://127.0.0.1:") || origin.startsWith("http://localhost:");
    }

    private boolean dispatchThroughBaritoneEvent(String input, long requestId) {
        Object player = Mc.player();
        Object level = Mc.level();
        DebugLog.info(requestId, "BARITONE", "Player=" + (player != null) + ", world=" + (level != null));
        if (player == null || level == null) throw new IllegalStateException("Open a world or join a server first");
        if (!isBaritoneAvailable()) throw new IllegalStateException("Baritone API is not loaded");
        if (!input.startsWith("#")) throw new IllegalArgumentException("Only # prefixed Baritone commands are allowed");
        DebugLog.info(requestId, "BARITONE", "Dispatching through the same ChatEvent path used by Baritone's manual-chat mixin: " + input);
        try {
            Class<?> apiClass = Class.forName("baritone.api.BaritoneAPI");
            Object provider = apiClass.getMethod("getProvider").invoke(null);
            Method getForPlayer = null;
            for (Method candidate : provider.getClass().getMethods()) {
                if (candidate.getName().equals("getBaritoneForPlayer") && candidate.getParameterCount() == 1) {
                    getForPlayer = candidate;
                    break;
                }
            }
            if (getForPlayer == null) throw new NoSuchMethodException("getBaritoneForPlayer(player)");
            Object baritone = getForPlayer.invoke(provider, player);
            if (baritone == null) throw new IllegalStateException("No Baritone instance is associated with the current player");
            DebugLog.info(requestId, "BARITONE", "Resolved Baritone instance for current player: " + baritone.getClass().getName());

            Object eventHandler = baritone.getClass().getMethod("getGameEventHandler").invoke(baritone);
            Class<?> chatEventClass = Class.forName("baritone.api.event.events.ChatEvent");
            Object chatEvent = chatEventClass.getConstructor(String.class).newInstance(input);
            Method dispatch = eventHandler.getClass().getMethod("onSendChatMessage", chatEventClass);
            dispatch.invoke(eventHandler, chatEvent);

            Method isCancelled = chatEventClass.getMethod("isCancelled");
            boolean accepted = (boolean) isCancelled.invoke(chatEvent);
            DebugLog.info(requestId, "BARITONE", "ChatEvent returned; cancelled=" + accepted + " (true means Baritone consumed it)");
            return accepted;
        } catch (ReflectiveOperationException error) {
            throw new IllegalStateException("Baritone ChatEvent API is incompatible: " + rootMessage(error), error);
        }
    }

    private void warmBlockMetadata(String command, long requestId) {
        String trimmed = command.trim();
        boolean mine = trimmed.matches("(?i)^#mine(?:\\s+.*)?$");
        boolean quota = trimmed.matches("(?i)^#minequota\\s+.*$");
        boolean blockGoto = trimmed.matches("(?i)^#goto\\s+\\S+$")
                && !trimmed.substring(trimmed.indexOf(' ') + 1).matches("~?(?:-?\\d+(?:\\.\\d+)?)?");
        if (!mine && !quota && !blockGoto) return;
        int commandLength = quota ? 10 : 5;
        String[] parts = trimmed.substring(commandLength).trim().split("\\s+");
        if (parts.length == 0 || parts[0].isBlank()) return;
        DebugLog.info(requestId, "WARMUP", "Preloading Baritone block metadata off the Render thread");
        try {
            Class<?> blockMeta = Class.forName("baritone.api.utils.BlockOptionalMeta");
            var constructor = blockMeta.getConstructor(String.class);
            int warmed = 0;
            for (String raw : parts) {
                String selector = quota ? raw.substring(0, raw.lastIndexOf('=')) : raw;
                if (mine && selector.matches("\\d+") && warmed == 0) continue;
                DebugLog.info(requestId, "WARMUP", "Loading selector: " + selector);
                constructor.newInstance(selector);
                warmed++;
            }
            DebugLog.info(requestId, "WARMUP", "Block metadata ready; selectors=" + warmed);
        } catch (ReflectiveOperationException error) {
            throw new IllegalStateException("Could not preload Baritone block metadata: " + rootMessage(error), error);
        }
    }

    private boolean startQuotaMining(String command, long requestId) {
        Object player = Mc.player();
        if (player == null || Mc.level() == null) throw new IllegalStateException("Open a world or join a server first");
        try {
            Class<?> metaClass = Class.forName("baritone.api.utils.BlockOptionalMeta");
            Class<?> itemStackClass = Class.forName("net.minecraft.world.item.ItemStack");
            Method matches = metaClass.getMethod("matches", itemStackClass);
            String[] specs = command.substring(11).trim().split("\\s+");
            java.util.List<QuotaTarget> targets = new java.util.ArrayList<>();
            for (String spec : specs) {
                int separator = spec.lastIndexOf('=');
                if (separator <= 0 || separator == spec.length() - 1) throw new IllegalArgumentException("Invalid mine quota: " + spec);
                String selector = spec.substring(0, separator);
                int desired = Integer.parseInt(spec.substring(separator + 1));
                if (desired <= 0) throw new IllegalArgumentException("Mine quota must be greater than zero");
                Object matcher = metaClass.getConstructor(String.class).newInstance(selector);
                int baseline = countMatchingItems(matcher, matches);
                targets.add(new QuotaTarget(selector, desired, baseline + desired, matcher, matches));
                DebugLog.info(requestId, "QUOTA", selector + ": baseline=" + baseline + ", requested=" + desired + ", target=" + (baseline + desired));
            }
            if (targets.isEmpty()) throw new IllegalArgumentException("No mine quotas supplied");
            quotaSession = new QuotaSession(targets, 0, requestId);
            return dispatchQuotaTarget(quotaSession);
        } catch (ReflectiveOperationException error) {
            throw new IllegalStateException("Could not start quota mining: " + rootMessage(error), error);
        }
    }

    private int countMatchingItems(Object matcher, Method matches) {
        Object player = Mc.player();
        if (player == null) return 0;
        Object inventory = Mc.inventory(player);
        int total = 0;
        for (int slot = 0; slot < Mc.inventorySize(inventory); slot++) {
            Object stack = Mc.inventoryItem(inventory, slot);
            if (!Mc.itemStackEmpty(stack)) {
                try { if ((boolean) matches.invoke(matcher, stack)) total += Mc.itemCount(stack); }
                catch (ReflectiveOperationException error) { throw new IllegalStateException(rootMessage(error), error); }
            }
        }
        return total;
    }

    private boolean dispatchQuotaTarget(QuotaSession session) {
        QuotaTarget target = session.targets().get(session.index());
        DebugLog.info(session.requestId(), "QUOTA", "Starting " + target.selector() + " until inventory total reaches " + target.absoluteTarget());
        return dispatchThroughBaritoneEvent("#mine " + target.absoluteTarget() + " " + target.selector(), session.requestId());
    }

    private void checkQuotaProgress() {
        QuotaSession session = quotaSession;
        if (session == null || Mc.player() == null) return;
        QuotaTarget target = session.targets().get(session.index());
        int current = countMatchingItems(target.matcher(), target.matchesMethod());
        if (current < target.absoluteTarget()) return;
        DebugLog.info(session.requestId(), "QUOTA", "Completed " + target.selector() + ": current=" + current);
        int nextIndex = session.index() + 1;
        if (nextIndex >= session.targets().size()) {
            quotaSession = null;
            DebugLog.info(session.requestId(), "QUOTA", "All mining quotas completed");
            dispatchThroughBaritoneEvent("#cancel", session.requestId());
            return;
        }
        QuotaSession next = new QuotaSession(session.targets(), nextIndex, session.requestId());
        quotaSession = next;
        dispatchQuotaTarget(next);
    }

    private record QuotaTarget(String selector, int desired, int absoluteTarget, Object matcher, Method matchesMethod) {}
    private record QuotaSession(java.util.List<QuotaTarget> targets, int index, long requestId) {}

    private boolean isBaritoneAvailable() {
        try { Class.forName("baritone.api.BaritoneAPI"); return true; }
        catch (ClassNotFoundException ignored) { return false; }
    }

    private String modVersion(String id) {
        try {
            Class<?> modListClass = Class.forName("net.minecraftforge.fml.ModList");
            Object modList = modListClass.getMethod("get").invoke(null);
            Object optional = modListClass.getMethod("getModContainerById", String.class).invoke(modList, id);
            if (!(optional instanceof Optional<?> opt) || opt.isEmpty()) return "not-found";
            Object container = opt.get();
            Object info = container.getClass().getMethod("getModInfo").invoke(container);
            Object version = info.getClass().getMethod("getVersion").invoke(info);
            return String.valueOf(version);
        } catch (Throwable ignored) {
            return "not-found";
        }
    }

    private void fail(HttpExchange exchange, int status, String message, long requestId) throws IOException {
        DebugLog.info(requestId, "RESPONSE", status + " " + message);
        respond(exchange, status, "{\"ok\":false,\"error\":\"" + jsonEscape(message) + "\",\"requestId\":" + requestId + "}", requestId);
    }

    private static String readCommand(String json) {
        Matcher matcher = COMMAND_FIELD.matcher(json);
        return matcher.find() ? unescapeJson(matcher.group(1)) : null;
    }

    private static String readStringField(String json, Pattern pattern) {
        Matcher matcher = pattern.matcher(json);
        return matcher.find() ? unescapeJson(matcher.group(1)) : null;
    }

    private static int readIntField(String json, String field, int fallback) {
        Matcher matcher = Pattern.compile("\\\"" + Pattern.quote(field) + "\\\"\\s*:\\s*(-?\\d+)").matcher(json);
        if (!matcher.find()) return fallback;
        try { return Integer.parseInt(matcher.group(1)); }
        catch (NumberFormatException ignored) { return fallback; }
    }

    private static String unescapeJson(String value) {
        return value.replace("\\\"", "\"").replace("\\\\", "\\").replace("\\n", "\n").replace("\\r", "\r").replace("\\t", "\t");
    }

    private static long elapsedMs(long nanoStart) { return TimeUnit.NANOSECONDS.toMillis(System.nanoTime() - nanoStart); }
    private static String rootMessage(Throwable error) {
        Throwable current = error;
        while ((current instanceof InvocationTargetException || current.getCause() != null) && current.getCause() != null) current = current.getCause();
        return current.getMessage() == null ? current.getClass().getSimpleName() : current.getMessage();
    }
    private static String jsonEscape(String value) { return value.replace("\\", "\\\\").replace("\"", "\\\"").replace("\n", "\\n").replace("\r", "\\r"); }

    private static void respondBytes(HttpExchange exchange, int status, String contentType, byte[] bytes, long requestId, String cacheControl) throws IOException {
        exchange.getResponseHeaders().set("Content-Type", contentType);
        exchange.getResponseHeaders().set("Cache-Control", cacheControl);
        try {
            exchange.sendResponseHeaders(status, bytes.length);
            exchange.getResponseBody().write(bytes);
        } catch (IOException error) {
            DebugLog.error(requestId, "HTTP", "Could not write binary response; browser may have disconnected", error);
            throw error;
        } finally {
            exchange.close();
        }
    }

    private static void respond(HttpExchange exchange, int status, String json, long requestId) throws IOException {
        byte[] bytes = json.getBytes(StandardCharsets.UTF_8);
        exchange.getResponseHeaders().set("Content-Type", "application/json; charset=utf-8");
        exchange.getResponseHeaders().set("Cache-Control", "no-store");
        try {
            exchange.sendResponseHeaders(status, bytes.length);
            exchange.getResponseBody().write(bytes);
        } catch (IOException error) {
            DebugLog.error(requestId, "HTTP", "Could not write response; browser may have disconnected", error);
            throw error;
        } finally {
            exchange.close();
        }
    }

    /**
     * Runtime adapter for Forge's SRG-named Minecraft classes.
     * This deliberately keeps net.minecraft members out of the bytecode linkage, so the jar
     * does not need a ForgeGradle reobfuscation pass. Candidate names include the 1.19.2 SRG
     * names first and Mojmap names second, which also makes local/dev launches easier.
     */
    private static final class Mc {
        private static final String MINECRAFT = "net.minecraft.client.Minecraft";
        private static final String ITEM_STACK = "net.minecraft.world.item.ItemStack";
        private static final String CLICK_TYPE = "net.minecraft.world.inventory.ClickType";
        private static final String ABSTRACT_CONTAINER_SCREEN = "net.minecraft.client.gui.screens.inventory.AbstractContainerScreen";

        static boolean isClientEnvironment() {
            try {
                Class.forName(MINECRAFT, false, BaritoneWebBridge.class.getClassLoader());
                return true;
            } catch (ClassNotFoundException ignored) {
                return false;
            }
        }

        static Object minecraft() {
            try { return invokeStatic(Class.forName(MINECRAFT), new String[]{"m_91087_", "getInstance"}); }
            catch (Throwable error) { return null; }
        }

        static Object player() {
            Object mc = minecraft();
            return mc == null ? null : fieldOrNull(mc, "f_91074_", "player");
        }

        static Object level() {
            Object mc = minecraft();
            return mc == null ? null : fieldOrNull(mc, "f_91073_", "level");
        }

        static byte[] readActiveResource(String entryName) {
            if (entryName == null || !entryName.startsWith("assets/")) return null;
            try {
                int namespaceStart = "assets/".length();
                int slash = entryName.indexOf('/', namespaceStart);
                if (slash < 0 || slash + 1 >= entryName.length()) return null;
                String namespace = entryName.substring(namespaceStart, slash);
                String path = entryName.substring(slash + 1);

                Object mc = minecraft();
                if (mc == null) return null;
                Class<?> managerClass = Class.forName("net.minecraft.server.packs.resources.ResourceManager");
                Method getManager = null;
                for (Method candidate : mc.getClass().getMethods()) {
                    if (candidate.getParameterCount() == 0 && managerClass.isAssignableFrom(candidate.getReturnType())) {
                        getManager = candidate;
                        break;
                    }
                }
                if (getManager == null) return null;
                Object manager = getManager.invoke(mc);
                if (manager == null) return null;

                Class<?> locationClass = Class.forName("net.minecraft.resources.ResourceLocation");
                Object location;
                try { location = locationClass.getConstructor(String.class, String.class).newInstance(namespace, path); }
                catch (NoSuchMethodException ignored) { location = locationClass.getConstructor(String.class).newInstance(namespace + ":" + path); }

                Method getResource = null;
                for (Method candidate : manager.getClass().getMethods()) {
                    Class<?>[] p = candidate.getParameterTypes();
                    if (p.length == 1 && p[0].isAssignableFrom(locationClass)
                            && Optional.class.isAssignableFrom(candidate.getReturnType())) {
                        if (candidate.getName().equals("getResource")) { getResource = candidate; break; }
                        if (getResource == null) getResource = candidate;
                    }
                }
                if (getResource == null) return null;
                Object optionalValue = getResource.invoke(manager, location);
                if (!(optionalValue instanceof Optional<?> optional) || optional.isEmpty()) return null;
                Object resource = optional.get();

                Method open = null;
                for (Method candidate : resource.getClass().getMethods()) {
                    if (candidate.getParameterCount() == 0 && InputStream.class.isAssignableFrom(candidate.getReturnType())) {
                        if (candidate.getName().equals("open")) { open = candidate; break; }
                        if (open == null) open = candidate;
                    }
                }
                if (open == null) return null;
                try (InputStream input = (InputStream) open.invoke(resource)) { return input.readAllBytes(); }
            } catch (InvocationTargetException error) {
                return null;
            } catch (Throwable error) {
                return null;
            }
        }

        static Integer spawnEggColor(String itemId, int layer) {
            try {
                Class<?> spawnEggClass = Class.forName("net.minecraft.world.item.SpawnEggItem");
                Object item = itemById(itemId);
                if (item == null || !spawnEggClass.isInstance(item)) return null;
                Method color = null;
                for (Method candidate : spawnEggClass.getMethods()) {
                    Class<?>[] p = candidate.getParameterTypes();
                    if (p.length == 1 && p[0] == int.class && candidate.getReturnType() == int.class) {
                        if (candidate.getName().equals("getColor")) { color = candidate; break; }
                        if (color == null) color = candidate;
                    }
                }
                if (color == null) return null;
                return ((Number) color.invoke(item, layer)).intValue() & 0x00ffffff;
            } catch (Throwable ignored) {
                return null;
            }
        }

        private static Object itemById(String itemId) {
            try {
                Class<?> locationClass = Class.forName("net.minecraft.resources.ResourceLocation");
                Object location;
                int colon = itemId.indexOf(':');
                String namespace = itemId.substring(0, colon);
                String path = itemId.substring(colon + 1);
                try { location = locationClass.getConstructor(String.class, String.class).newInstance(namespace, path); }
                catch (NoSuchMethodException ignored) { location = locationClass.getConstructor(String.class).newInstance(itemId); }

                Class<?> forgeRegistries = Class.forName("net.minecraftforge.registries.ForgeRegistries");
                Object items = forgeRegistries.getField("ITEMS").get(null);
                Class<?> registryApi = Class.forName("net.minecraftforge.registries.IForgeRegistry");
                Method getValue = registryApi.getMethod("getValue", locationClass);
                return getValue.invoke(items, location);
            } catch (Throwable ignored) {
                return null;
            }
        }

        static Object gameMode() {
            Object mc = minecraft();
            return mc == null ? null : fieldOrNull(mc, "f_91072_", "gameMode");
        }

        static void execute(Runnable runnable) {
            Object mc = minecraft();
            if (mc == null) throw new IllegalStateException("Minecraft client is not available");
            if (mc instanceof Executor executor) {
                executor.execute(runnable);
                return;
            }
            invoke(mc, new String[]{"execute"}, new Class<?>[]{Runnable.class}, runnable);
        }

        static String sessionUserName() {
            try {
                Object mc = minecraft();
                if (mc == null) return "unknown";
                Object user = invokeNoArgs(mc, "m_91094_", "getUser");
                Object name = invokeNoArgsOrNull(user, "getName");
                return name == null ? "unknown" : String.valueOf(name);
            } catch (Throwable ignored) { return "unknown"; }
        }

        static Object inventory(Object player) { return invokeNoArgs(player, "m_150109_", "getInventory"); }
        static int inventorySize(Object inventory) { return intValue(inventory, new String[]{"m_6643_", "getContainerSize"}); }
        static Object inventoryItem(Object inventory, int slot) {
            return invoke(inventory, new String[]{"m_8020_", "getItem"}, new Class<?>[]{int.class}, slot);
        }

        static Object containerMenu(Object player) { return field(player, "f_36096_", "containerMenu"); }
        static Object inventoryMenu(Object player) { return field(player, "f_36095_", "inventoryMenu"); }

        @SuppressWarnings("unchecked")
        static List<?> slots(Object menu) {
            Object result = field(menu, "f_38839_", "slots");
            if (!(result instanceof List<?> list)) throw new IllegalStateException("Container slots field is not a List");
            return list;
        }

        static int containerId(Object menu) { return ((Number) field(menu, "f_38840_", "containerId")).intValue(); }
        static Object carried(Object menu) { return invokeNoArgs(menu, "m_142621_", "getCarried"); }
        static Object slotContainer(Object slot) { return field(slot, "f_40218_", "container"); }
        static int slotContainerIndex(Object slot) { return intValue(slot, new String[]{"m_150661_", "getContainerSlot", "getSlotIndex"}); }
        static Object slotItem(Object slot) { return invokeNoArgs(slot, "m_7993_", "getItem"); }

        static boolean itemStackEmpty(Object stack) {
            if (stack == null) return true;
            Object value = invokeNoArgs(stack, "m_41619_", "isEmpty");
            return Boolean.TRUE.equals(value);
        }

        static Object copyStack(Object stack) {
            if (stack == null) return null;
            try { return invokeNoArgs(stack, "m_41777_", "copy"); }
            catch (Throwable error) {
                Class<?> type = stack.getClass();
                for (Method method : type.getMethods()) {
                    if (method.getParameterCount() == 0 && type.isAssignableFrom(method.getReturnType())) {
                        try { return invokeMethod(method, stack); }
                        catch (Throwable ignored) { }
                    }
                }
                return stack;
            }
        }

        static String stackRenderIdentity(Object stack) {
            Object snapshot = copyStack(stack);
            if (snapshot == null) return "null";
            try { invoke(snapshot, new String[]{"m_41764_", "setCount"}, new Class<?>[]{int.class}, 1); }
            catch (Throwable ignored) { }
            Object serialized = invokeNoArgsOrNull(snapshot, "serializeNBT");
            if (serialized == null) serialized = invokeNoArgsOrNull(snapshot, "m_41783_", "getTag");
            String data = serialized == null ? "" : serialized.toString();
            return "damage=" + itemDamage(snapshot) + "|nbt=" + data;
        }

        static byte[] renderItemStackIconPng(Object stack, int outputSize) {
            if (stack == null || itemStackEmpty(stack)) return null;
            Object mc = minecraft();
            if (mc == null) throw new IllegalStateException("Minecraft client is not available");
            int[] oldViewport = Gl.viewport();
            int oldFramebuffer = Gl.getInteger(Gl.GL_FRAMEBUFFER_BINDING);
            boolean oldScissor = Gl.isEnabled(Gl.GL_SCISSOR_TEST);
            if (oldViewport[2] <= 0 || oldViewport[3] <= 0) throw new IllegalStateException("Minecraft viewport is not available");

            // The 2.5.0 renderer reused whatever projection happened to be active when the HTTP
            // request reached the Render thread. Between normal frames that projection is often
            // the world projection, so ItemRenderer successfully executed but every fragment
            // landed outside our FBO. Build the same 16x16 logical GUI projection that Minecraft
            // installs before drawing screens, then scale it to a 64x64 physical render target.
            Gl.ensureTarget(outputSize);
            GuiCaptureState guiState = null;
            try {
                Gl.bindTarget();
                Gl.viewport(0, 0, outputSize, outputSize);
                Gl.disable(Gl.GL_SCISSOR_TEST);
                // Render tasks may run between normal frames. Do not inherit a temporary
                // write-mask left by a world/post-processing pass.
                Gl.colorMask(true, true, true, true);
                Gl.depthMask(true);
                Gl.clearTransparent();
                guiState = beginGuiCapture(16.0f);
                renderGuiItem(mc, stack);
                Gl.finish();
                BufferedImage captured = Gl.readImage(outputSize);
                int visible = countVisiblePixels(captured);
                if (visible < 4) {
                    throw new IllegalStateException("Minecraft produced a transparent icon after explicit GUI projection/model-view setup");
                }
                ByteArrayOutputStream output = new ByteArrayOutputStream();
                ImageIO.write(captured, "PNG", output);
                return output.toByteArray();
            } catch (IOException error) {
                throw new IllegalStateException("Could not encode rendered item icon", error);
            } finally {
                if (guiState != null) guiState.restore();
                Gl.bindFramebuffer(oldFramebuffer);
                Gl.viewport(oldViewport[0], oldViewport[1], oldViewport[2], oldViewport[3]);
                if (oldScissor) Gl.enable(Gl.GL_SCISSOR_TEST);
                else Gl.disable(Gl.GL_SCISSOR_TEST);
            }
        }

        private static GuiCaptureState beginGuiCapture(float logicalSize) {
            try {
                Class<?> matrixClass = Class.forName("com.mojang.math.Matrix4f");
                Class<?> renderSystem = Class.forName("com.mojang.blaze3d.systems.RenderSystem");
                Method ortho = findMethod(matrixClass, new String[]{"m_162203_", "projectionMatrix"},
                        new Class<?>[]{float.class, float.class, float.class, float.class, float.class, float.class});
                Method setProjection = findMethod(renderSystem, new String[]{"m_157425_", "setProjectionMatrix"},
                        new Class<?>[]{matrixClass});
                Method getModelView = findMethod(renderSystem, new String[]{"m_157191_", "getModelViewStack"}, new Class<?>[0]);
                Method applyModelView = findMethod(renderSystem, new String[]{"m_157182_", "applyModelViewMatrix"}, new Class<?>[0]);
                if (!Modifier.isStatic(ortho.getModifiers()) || !Modifier.isStatic(setProjection.getModifiers())
                        || !Modifier.isStatic(getModelView.getModifiers()) || !Modifier.isStatic(applyModelView.getModifiers())) {
                    throw new IllegalStateException("Minecraft GUI matrix methods have an unexpected signature");
                }

                float farPlane = guiFarPlane();
                Object projection = invokeMethod(ortho, null, 0.0f, logicalSize, 0.0f, logicalSize, 1000.0f, farPlane);

                // Capture the exact RenderSystem projection object before replacing it. In
                // 1.19.2 setProjectionMatrix stores the supplied Matrix4f in a static field.
                // Discover that field by identity so this remains independent of its obfuscated
                // field name, then restore it when the icon has been captured.
                Map<Field, Object> before = new LinkedHashMap<>();
                for (Field field : renderSystem.getDeclaredFields()) {
                    if (!Modifier.isStatic(field.getModifiers()) || field.getType() != matrixClass) continue;
                    try {
                        field.setAccessible(true);
                        before.put(field, field.get(null));
                    } catch (Throwable ignored) { }
                }
                invokeMethod(setProjection, null, projection);
                Object oldProjection = null;
                for (Map.Entry<Field, Object> entry : before.entrySet()) {
                    try {
                        if (entry.getKey().get(null) == projection) {
                            oldProjection = entry.getValue();
                            break;
                        }
                    } catch (Throwable ignored) { }
                }

                Object poseStack = invokeMethod(getModelView, null);
                invokeNoArgs(poseStack, "m_85836_", "pushPose");
                boolean pushed = true;
                try {
                    invokeNoArgs(poseStack, "m_166856_", "setIdentity");
                    invoke(poseStack, new String[]{"m_85837_", "translate"},
                            new Class<?>[]{double.class, double.class, double.class},
                            0.0d, 0.0d, (double) (1000.0f - farPlane));
                    invokeMethod(applyModelView, null);
                    setupGuiLighting();
                    return new GuiCaptureState(setProjection, oldProjection, poseStack, applyModelView, pushed);
                } catch (Throwable error) {
                    if (pushed) {
                        try { invokeNoArgs(poseStack, "m_85849_", "popPose"); } catch (Throwable ignored) { }
                        try { invokeMethod(applyModelView, null); } catch (Throwable ignored) { }
                    }
                    if (oldProjection != null) {
                        try { invokeMethod(setProjection, null, oldProjection); } catch (Throwable ignored) { }
                    }
                    throw error;
                }
            } catch (Throwable error) {
                throw new IllegalStateException("Could not install Minecraft GUI render state: " + rootMessage(error), error);
            }
        }

        private static float guiFarPlane() {
            try {
                Class<?> hooks = Class.forName("net.minecraftforge.client.ForgeHooksClient");
                Method method = hooks.getMethod("getGuiFarPlane");
                Object value = method.invoke(null);
                if (value instanceof Number number && number.floatValue() > 1000.0f) return number.floatValue();
            } catch (Throwable ignored) { }
            return 3000.0f;
        }

        private static void setupGuiLighting() {
            try {
                Class<?> lighting = Class.forName("net.minecraft.client.renderer.Lighting");
                Method method = findMethod(lighting, new String[]{"m_84931_", "setupFor3DItems"}, new Class<?>[0]);
                if (Modifier.isStatic(method.getModifiers())) invokeMethod(method, null);
            } catch (Throwable ignored) { }
        }

        private static final class GuiCaptureState {
            private final Method setProjection;
            private final Object oldProjection;
            private final Object poseStack;
            private final Method applyModelView;
            private final boolean pushed;
            private boolean restored;

            private GuiCaptureState(Method setProjection, Object oldProjection, Object poseStack, Method applyModelView, boolean pushed) {
                this.setProjection = setProjection;
                this.oldProjection = oldProjection;
                this.poseStack = poseStack;
                this.applyModelView = applyModelView;
                this.pushed = pushed;
            }

            void restore() {
                if (restored) return;
                restored = true;
                if (pushed) {
                    try { invokeNoArgs(poseStack, "m_85849_", "popPose"); } catch (Throwable ignored) { }
                    try { invokeMethod(applyModelView, null); } catch (Throwable ignored) { }
                }
                if (oldProjection != null) {
                    try { invokeMethod(setProjection, null, oldProjection); } catch (Throwable ignored) { }
                }
                setupGuiLighting();
            }
        }

        private static int countVisiblePixels(BufferedImage image) {
            int visible = 0;
            for (int y = 0; y < image.getHeight(); y++) {
                for (int x = 0; x < image.getWidth(); x++) {
                    if (((image.getRGB(x, y) >>> 24) & 0xff) > 3 && ++visible >= 4) return visible;
                }
            }
            return visible;
        }

        private static double windowGuiScale(Object mc) {
            try {
                Class<?> windowClass = Class.forName("com.mojang.blaze3d.platform.Window");
                Object window = null;
                for (Method method : mc.getClass().getMethods()) {
                    if (method.getParameterCount() == 0 && windowClass.isAssignableFrom(method.getReturnType())) {
                        window = method.invoke(mc);
                        if (window != null) break;
                    }
                }
                if (window == null) return 0.0;
                for (String name : new String[]{"getGuiScale"}) {
                    try {
                        Method method = window.getClass().getMethod(name);
                        Object value = method.invoke(window);
                        if (value instanceof Number number && number.doubleValue() > 0.0) return number.doubleValue();
                    } catch (Throwable ignored) { }
                }
                for (Method method : window.getClass().getMethods()) {
                    if (method.getParameterCount() != 0) continue;
                    if (method.getReturnType() != double.class && method.getReturnType() != Double.class) continue;
                    try {
                        double value = ((Number) method.invoke(window)).doubleValue();
                        if (value >= 0.5 && value <= 16.0) return value;
                    } catch (Throwable ignored) { }
                }
            } catch (Throwable ignored) { }
            return 0.0;
        }

        private static void renderGuiItem(Object mc, Object stack) {
            try {
                Class<?> rendererClass = Class.forName("net.minecraft.client.renderer.entity.ItemRenderer");
                Class<?> stackClass = Class.forName(ITEM_STACK);
                Object renderer = null;
                for (Method method : mc.getClass().getMethods()) {
                    if (method.getParameterCount() == 0 && rendererClass.isAssignableFrom(method.getReturnType())) {
                        try {
                            renderer = method.invoke(mc);
                            if (renderer != null) break;
                        } catch (Throwable ignored) { }
                    }
                }
                if (renderer == null) {
                    for (Class<?> current = mc.getClass(); current != null && renderer == null; current = current.getSuperclass()) {
                        for (Field field : current.getDeclaredFields()) {
                            if (!rendererClass.isAssignableFrom(field.getType())) continue;
                            try {
                                field.setAccessible(true);
                                renderer = field.get(mc);
                                if (renderer != null) break;
                            } catch (Throwable ignored) { }
                        }
                    }
                }
                if (renderer == null) throw new IllegalStateException("Could not locate Minecraft ItemRenderer");

                Object player = player();
                Method threeArg = null;
                Method fiveArg = null;
                for (Class<?> current = renderer.getClass(); current != null; current = current.getSuperclass()) {
                    for (Method method : current.getDeclaredMethods()) {
                        if (method.getReturnType() != void.class) continue;
                        Class<?>[] p = method.getParameterTypes();
                        if (p.length == 5 && stackClass.isAssignableFrom(p[1]) && p[2] == int.class && p[3] == int.class && p[4] == int.class
                                && (player == null || p[0].isAssignableFrom(player.getClass()))) {
                            fiveArg = method;
                            break;
                        }
                        if (p.length == 3 && stackClass.isAssignableFrom(p[0]) && p[1] == int.class && p[2] == int.class && threeArg == null) {
                            threeArg = method;
                        }
                    }
                    if (fiveArg != null) break;
                }
                if (fiveArg != null) {
                    fiveArg.setAccessible(true);
                    fiveArg.invoke(renderer, player, stack, 0, 0, 0);
                    return;
                }
                if (threeArg != null) {
                    threeArg.setAccessible(true);
                    threeArg.invoke(renderer, stack, 0, 0);
                    return;
                }
                throw new NoSuchMethodException("ItemRenderer GUI item render method");
            } catch (InvocationTargetException error) {
                Throwable cause = error.getCause() == null ? error : error.getCause();
                throw new IllegalStateException("Minecraft ItemRenderer failed: " + rootMessage(cause), cause);
            } catch (Throwable error) {
                throw new IllegalStateException("Could not render ItemStack through Minecraft: " + rootMessage(error), error);
            }
        }

        private static final class Gl {
            static final int GL_TEXTURE_2D = 3553;
            static final int GL_RGBA = 6408;
            static final int GL_RGBA8 = 32856;
            static final int GL_UNSIGNED_BYTE = 5121;
            static final int GL_TEXTURE_MIN_FILTER = 10241;
            static final int GL_TEXTURE_MAG_FILTER = 10240;
            static final int GL_NEAREST = 9728;
            static final int GL_TEXTURE_WRAP_S = 10242;
            static final int GL_TEXTURE_WRAP_T = 10243;
            static final int GL_CLAMP_TO_EDGE = 33071;
            static final int GL_TEXTURE_BINDING_2D = 32873;
            static final int GL_VIEWPORT = 2978;
            static final int GL_SCISSOR_TEST = 3089;
            static final int GL_COLOR_BUFFER_BIT = 16384;
            static final int GL_DEPTH_BUFFER_BIT = 256;
            static final int GL_FRAMEBUFFER = 36160;
            static final int GL_FRAMEBUFFER_BINDING = 36006;
            static final int GL_COLOR_ATTACHMENT0 = 36064;
            static final int GL_RENDERBUFFER = 36161;
            static final int GL_RENDERBUFFER_BINDING = 36007;
            static final int GL_DEPTH_COMPONENT24 = 33190;
            static final int GL_DEPTH_ATTACHMENT = 36096;
            static final int GL_FRAMEBUFFER_COMPLETE = 36053;
            private static int framebuffer;
            private static int colorTexture;
            private static int depthBuffer;
            private static int targetSize;

            static synchronized void ensureTarget(int size) {
                if (framebuffer != 0 && targetSize == size) return;
                try {
                    Class<?> gl11 = Class.forName("org.lwjgl.opengl.GL11");
                    Class<?> gl30 = Class.forName("org.lwjgl.opengl.GL30");
                    int previousFramebuffer = getInteger(GL_FRAMEBUFFER_BINDING);
                    int previousTexture = getInteger(GL_TEXTURE_BINDING_2D);
                    int previousRenderbuffer = getInteger(GL_RENDERBUFFER_BINDING);
                    framebuffer = ((Number) gl30.getMethod("glGenFramebuffers").invoke(null)).intValue();
                    colorTexture = ((Number) gl11.getMethod("glGenTextures").invoke(null)).intValue();
                    depthBuffer = ((Number) gl30.getMethod("glGenRenderbuffers").invoke(null)).intValue();
                    gl30.getMethod("glBindFramebuffer", int.class, int.class).invoke(null, GL_FRAMEBUFFER, framebuffer);
                    gl11.getMethod("glBindTexture", int.class, int.class).invoke(null, GL_TEXTURE_2D, colorTexture);
                    gl11.getMethod("glTexParameteri", int.class, int.class, int.class).invoke(null, GL_TEXTURE_2D, GL_TEXTURE_MIN_FILTER, GL_NEAREST);
                    gl11.getMethod("glTexParameteri", int.class, int.class, int.class).invoke(null, GL_TEXTURE_2D, GL_TEXTURE_MAG_FILTER, GL_NEAREST);
                    gl11.getMethod("glTexParameteri", int.class, int.class, int.class).invoke(null, GL_TEXTURE_2D, GL_TEXTURE_WRAP_S, GL_CLAMP_TO_EDGE);
                    gl11.getMethod("glTexParameteri", int.class, int.class, int.class).invoke(null, GL_TEXTURE_2D, GL_TEXTURE_WRAP_T, GL_CLAMP_TO_EDGE);
                    gl11.getMethod("glTexImage2D", int.class, int.class, int.class, int.class, int.class, int.class, int.class, int.class, ByteBuffer.class)
                            .invoke(null, GL_TEXTURE_2D, 0, GL_RGBA8, size, size, 0, GL_RGBA, GL_UNSIGNED_BYTE, null);
                    gl30.getMethod("glFramebufferTexture2D", int.class, int.class, int.class, int.class, int.class)
                            .invoke(null, GL_FRAMEBUFFER, GL_COLOR_ATTACHMENT0, GL_TEXTURE_2D, colorTexture, 0);
                    gl30.getMethod("glBindRenderbuffer", int.class, int.class).invoke(null, GL_RENDERBUFFER, depthBuffer);
                    gl30.getMethod("glRenderbufferStorage", int.class, int.class, int.class, int.class)
                            .invoke(null, GL_RENDERBUFFER, GL_DEPTH_COMPONENT24, size, size);
                    gl30.getMethod("glFramebufferRenderbuffer", int.class, int.class, int.class, int.class)
                            .invoke(null, GL_FRAMEBUFFER, GL_DEPTH_ATTACHMENT, GL_RENDERBUFFER, depthBuffer);
                    int status = ((Number) gl30.getMethod("glCheckFramebufferStatus", int.class).invoke(null, GL_FRAMEBUFFER)).intValue();
                    if (status != GL_FRAMEBUFFER_COMPLETE) throw new IllegalStateException("Off-screen framebuffer incomplete: 0x" + Integer.toHexString(status));
                    targetSize = size;
                    gl11.getMethod("glBindTexture", int.class, int.class).invoke(null, GL_TEXTURE_2D, previousTexture);
                    gl30.getMethod("glBindRenderbuffer", int.class, int.class).invoke(null, GL_RENDERBUFFER, previousRenderbuffer);
                    gl30.getMethod("glBindFramebuffer", int.class, int.class).invoke(null, GL_FRAMEBUFFER, previousFramebuffer);
                } catch (InvocationTargetException error) {
                    Throwable cause = error.getCause() == null ? error : error.getCause();
                    throw new IllegalStateException("Could not create off-screen framebuffer: " + rootMessage(cause), cause);
                } catch (Throwable error) {
                    throw new IllegalStateException("Could not create off-screen framebuffer: " + rootMessage(error), error);
                }
            }

            static void bindTarget() { bindFramebuffer(framebuffer); }

            static void bindFramebuffer(int id) {
                try { Class.forName("org.lwjgl.opengl.GL30").getMethod("glBindFramebuffer", int.class, int.class).invoke(null, GL_FRAMEBUFFER, id); }
                catch (Throwable error) { throw new IllegalStateException("Could not bind framebuffer", error); }
            }

            static int getInteger(int pname) {
                try { return ((Number) Class.forName("org.lwjgl.opengl.GL11").getMethod("glGetInteger", int.class).invoke(null, pname)).intValue(); }
                catch (Throwable error) { throw new IllegalStateException("Could not query OpenGL integer state", error); }
            }

            static boolean isEnabled(int capability) {
                try { return (boolean) Class.forName("org.lwjgl.opengl.GL11").getMethod("glIsEnabled", int.class).invoke(null, capability); }
                catch (Throwable error) { throw new IllegalStateException("Could not query OpenGL capability", error); }
            }

            static void enable(int capability) {
                try { Class.forName("org.lwjgl.opengl.GL11").getMethod("glEnable", int.class).invoke(null, capability); }
                catch (Throwable error) { throw new IllegalStateException("Could not enable OpenGL capability", error); }
            }

            static void disable(int capability) {
                try { Class.forName("org.lwjgl.opengl.GL11").getMethod("glDisable", int.class).invoke(null, capability); }
                catch (Throwable error) { throw new IllegalStateException("Could not disable OpenGL capability", error); }
            }

            static void colorMask(boolean red, boolean green, boolean blue, boolean alpha) {
                try { Class.forName("org.lwjgl.opengl.GL11").getMethod("glColorMask", boolean.class, boolean.class, boolean.class, boolean.class)
                        .invoke(null, red, green, blue, alpha); }
                catch (Throwable error) { throw new IllegalStateException("Could not set OpenGL color mask", error); }
            }

            static void depthMask(boolean enabled) {
                try { Class.forName("org.lwjgl.opengl.GL11").getMethod("glDepthMask", boolean.class).invoke(null, enabled); }
                catch (Throwable error) { throw new IllegalStateException("Could not set OpenGL depth mask", error); }
            }

            static int[] viewport() {
                try {
                    IntBuffer buffer = ByteBuffer.allocateDirect(4 * Integer.BYTES).order(ByteOrder.nativeOrder()).asIntBuffer();
                    Class.forName("org.lwjgl.opengl.GL11").getMethod("glGetIntegerv", int.class, IntBuffer.class).invoke(null, GL_VIEWPORT, buffer);
                    return new int[]{buffer.get(0), buffer.get(1), buffer.get(2), buffer.get(3)};
                } catch (Throwable error) {
                    throw new IllegalStateException("Could not query OpenGL viewport", error);
                }
            }

            static void viewport(int x, int y, int width, int height) {
                try { Class.forName("org.lwjgl.opengl.GL11").getMethod("glViewport", int.class, int.class, int.class, int.class).invoke(null, x, y, width, height); }
                catch (Throwable error) { throw new IllegalStateException("Could not set OpenGL viewport", error); }
            }

            static void clearTransparent() {
                try {
                    Class<?> gl11 = Class.forName("org.lwjgl.opengl.GL11");
                    gl11.getMethod("glClearColor", float.class, float.class, float.class, float.class).invoke(null, 0f, 0f, 0f, 0f);
                    gl11.getMethod("glClearDepth", double.class).invoke(null, 1.0d);
                    gl11.getMethod("glClear", int.class).invoke(null, GL_COLOR_BUFFER_BIT | GL_DEPTH_BUFFER_BIT);
                } catch (Throwable error) { throw new IllegalStateException("Could not clear off-screen framebuffer", error); }
            }

            static void finish() {
                try { Class.forName("org.lwjgl.opengl.GL11").getMethod("glFinish").invoke(null); }
                catch (Throwable error) { throw new IllegalStateException("Could not finish OpenGL render", error); }
            }

            static BufferedImage readImage(int size) {
                try {
                    ByteBuffer pixels = ByteBuffer.allocateDirect(size * size * 4).order(ByteOrder.nativeOrder());
                    Class.forName("org.lwjgl.opengl.GL11")
                            .getMethod("glReadPixels", int.class, int.class, int.class, int.class, int.class, int.class, ByteBuffer.class)
                            .invoke(null, 0, 0, size, size, GL_RGBA, GL_UNSIGNED_BYTE, pixels);
                    BufferedImage image = new BufferedImage(size, size, BufferedImage.TYPE_INT_ARGB);
                    for (int y = 0; y < size; y++) {
                        int sourceY = size - 1 - y;
                        for (int x = 0; x < size; x++) {
                            int index = (sourceY * size + x) * 4;
                            int r = pixels.get(index) & 0xff;
                            int g = pixels.get(index + 1) & 0xff;
                            int b = pixels.get(index + 2) & 0xff;
                            int a = pixels.get(index + 3) & 0xff;
                            image.setRGB(x, y, (a << 24) | (r << 16) | (g << 8) | b);
                        }
                    }
                    return image;
                } catch (Throwable error) { throw new IllegalStateException("Could not read off-screen pixels", error); }
            }
        }

        static Object itemFromStack(Object stack) { return invokeNoArgs(stack, "m_41720_", "getItem"); }
        static int itemCount(Object stack) { return intValue(stack, new String[]{"m_41613_", "getCount"}); }
        static int itemDamage(Object stack) { return intValue(stack, new String[]{"m_41773_", "getDamageValue", "getDamage"}); }
        static int itemMaxDamage(Object stack) { return intValue(stack, new String[]{"m_41776_", "getMaxDamage"}); }

        static String itemName(Object stack) {
            Object component = invokeNoArgs(stack, "m_41786_", "getHoverName", "getName");
            if (component == null) return "";
            Object value = invokeNoArgsOrNull(component, "getString");
            if (value == null) value = invokeNoArgsOrNull(component, "m_130086_");
            return value == null ? component.toString() : String.valueOf(value);
        }

        static String itemId(Object stack) {
            try {
                Object item = itemFromStack(stack);
                Class<?> forgeRegistries = Class.forName("net.minecraftforge.registries.ForgeRegistries");
                Object items = forgeRegistries.getField("ITEMS").get(null);
                // ForgeRegistry has two public one-argument getKey overloads in 1.19.x:
                // getKey(V value) and getKey(int id). Reflection order is unspecified, so selecting
                // merely by name + parameter count can accidentally pick getKey(int) and fail
                // with "argument type mismatch" for every non-empty ItemStack. Resolve the
                // generic API method explicitly from IForgeRegistry instead.
                Class<?> registryApi = Class.forName("net.minecraftforge.registries.IForgeRegistry");
                Method getKey = registryApi.getMethod("getKey", Object.class);
                Object key = getKey.invoke(items, item);
                return key == null ? "unknown" : key.toString();
            } catch (Throwable error) {
                throw new IllegalStateException("Could not resolve item id: " + rootMessage(error), error);
            }
        }

        static String playerName(Object player) {
            try {
                Object profile = invokeNoArgs(player, "m_36316_", "getGameProfile");
                Object name = invokeNoArgs(profile, "getName");
                return String.valueOf(name);
            } catch (Throwable error) { return "unknown"; }
        }

        static String currentScreenTitle() {
            try {
                Object mc = minecraft();
                if (mc == null) return "";
                Object screen = fieldOrNull(mc, "f_91080_", "screen", "currentScreen");
                if (screen == null || !isInstanceOf(screen, ABSTRACT_CONTAINER_SCREEN)) return "";
                Object title = invokeNoArgs(screen, "m_96636_", "getTitle");
                Object text = invokeNoArgsOrNull(title, "getString");
                return text == null ? String.valueOf(title) : String.valueOf(text);
            } catch (Throwable ignored) { return ""; }
        }

        static void clickSlot(Object gameMode, Object menu, int slot, int button, String clickTypeName, Object player) {
            try {
                Class<?> clickTypeClass = Class.forName(CLICK_TYPE);
                @SuppressWarnings({"rawtypes", "unchecked"})
                Object clickType = Enum.valueOf((Class<? extends Enum>) clickTypeClass.asSubclass(Enum.class), clickTypeName);
                Method method = findInventoryClickMethod(gameMode.getClass(), clickTypeClass, player.getClass());
                method.invoke(gameMode, containerId(menu), slot, button, clickType, player);
            } catch (InvocationTargetException error) {
                Throwable cause = error.getCause() == null ? error : error.getCause();
                throw new IllegalStateException("Inventory click failed: " + rootMessage(cause), cause);
            } catch (Throwable error) {
                throw new IllegalStateException("Could not call inventory click: " + rootMessage(error), error);
            }
        }

        private static Method findInventoryClickMethod(Class<?> type, Class<?> clickTypeClass, Class<?> playerClass) throws NoSuchMethodException {
            for (Class<?> current = type; current != null; current = current.getSuperclass()) {
                for (Method method : current.getDeclaredMethods()) {
                    Class<?>[] p = method.getParameterTypes();
                    if (p.length == 5 && p[0] == int.class && p[1] == int.class && p[2] == int.class
                            && p[3] == clickTypeClass && p[4].isAssignableFrom(playerClass)) {
                        method.setAccessible(true);
                        return method;
                    }
                }
            }
            throw new NoSuchMethodException("handleInventoryMouseClick(int,int,int,ClickType,Player)");
        }

        static int intValue(Object target, String[] names) {
            Object value = invokeNoArgs(target, names);
            return ((Number) value).intValue();
        }

        static float floatValue(Object target, String[] names) {
            Object value = invokeNoArgs(target, names);
            return ((Number) value).floatValue();
        }

        static Object field(Object target, String... names) {
            if (target == null) throw new IllegalStateException("Reflection target is null for field " + String.join("/", names));
            Object value = readField(target, names);
            if (value == Missing.INSTANCE) throw new IllegalStateException("Could not find field " + String.join("/", names) + " in " + target.getClass().getName());
            return value;
        }

        private static Object fieldOrNull(Object target, String... names) {
            if (target == null) return null;
            Object value = readField(target, names);
            return value == Missing.INSTANCE ? null : value;
        }

        private static Object readField(Object target, String... names) {
            for (String name : names) {
                for (Class<?> current = target.getClass(); current != null; current = current.getSuperclass()) {
                    try {
                        Field field = current.getDeclaredField(name);
                        field.setAccessible(true);
                        return field.get(target);
                    } catch (NoSuchFieldException ignored) {
                    } catch (ReflectiveOperationException error) {
                        throw new IllegalStateException(error);
                    }
                }
            }
            return Missing.INSTANCE;
        }

        static Object invokeNoArgs(Object target, String... names) { return invoke(target, names, new Class<?>[0]); }

        private static Object invokeNoArgsOrNull(Object target, String... names) {
            if (target == null) return null;
            try { return invokeNoArgs(target, names); }
            catch (Throwable ignored) { return null; }
        }

        static Object invoke(Object target, String[] names, Class<?>[] parameterTypes, Object... args) {
            if (target == null) throw new IllegalStateException("Reflection target is null for " + String.join("/", names));
            Method method = findMethod(target.getClass(), names, parameterTypes);
            return invokeMethod(method, target, args);
        }

        private static Object invokeStatic(Class<?> type, String[] names, Object... args) {
            Class<?>[] params = new Class<?>[args.length];
            for (int i = 0; i < args.length; i++) params[i] = args[i].getClass();
            Method method = findMethod(type, names, params);
            if (!Modifier.isStatic(method.getModifiers())) throw new IllegalStateException(method + " is not static");
            return invokeMethod(method, null, args);
        }

        private static Method findMethod(Class<?> type, String[] names, Class<?>[] parameterTypes) {
            for (String name : names) {
                try { return type.getMethod(name, parameterTypes); }
                catch (NoSuchMethodException ignored) { }
                for (Class<?> current = type; current != null; current = current.getSuperclass()) {
                    try {
                        Method method = current.getDeclaredMethod(name, parameterTypes);
                        method.setAccessible(true);
                        return method;
                    } catch (NoSuchMethodException ignored) { }
                }
            }
            // Interface/default methods can be inherited through multiple levels. Try a signature scan as final fallback.
            for (Method method : type.getMethods()) {
                for (String name : names) {
                    if (method.getName().equals(name) && java.util.Arrays.equals(method.getParameterTypes(), parameterTypes)) return method;
                }
            }
            throw new IllegalStateException("Could not find method " + String.join("/", names) + " on " + type.getName());
        }

        private static Object invokeMethod(Method method, Object target, Object... args) {
            try {
                method.setAccessible(true);
                return method.invoke(target, args);
            } catch (InvocationTargetException error) {
                Throwable cause = error.getCause() == null ? error : error.getCause();
                throw new IllegalStateException(rootMessage(cause), cause);
            } catch (ReflectiveOperationException error) {
                throw new IllegalStateException(rootMessage(error), error);
            }
        }

        private static boolean isInstanceOf(Object object, String className) {
            try { return Class.forName(className).isInstance(object); }
            catch (ClassNotFoundException ignored) { return false; }
        }

        private enum Missing { INSTANCE }
    }

    private static final class DebugLog {
        private static final DateTimeFormatter TIME = DateTimeFormatter.ofPattern("yyyy-MM-dd HH:mm:ss.SSS").withZone(ZoneId.systemDefault());
        private static final LinkedBlockingQueue<String> QUEUE = new LinkedBlockingQueue<>(10_000);
        private static final String POISON = new String("STOP");
        private static volatile Path file;
        private static volatile Thread writer;

        static void start(Path logFile) {
            file = logFile;
            try {
                Files.createDirectories(logFile.getParent());
                if (Files.exists(logFile) && Files.size(logFile) > 8 * 1024 * 1024) {
                    Path previous = logFile.resolveSibling("baritone-web-bridge.previous.log");
                    Files.deleteIfExists(previous);
                    Files.move(logFile, previous);
                }
            } catch (IOException error) {
                System.err.println("[Baritone Web Bridge] Log initialization failed: " + error.getMessage());
            }
            writer = new Thread(DebugLog::writeLoop, "baritone-web-log-writer");
            writer.setDaemon(true);
            writer.start();
        }

        static void info(String category, String message) { enqueue(format("INFO", "-", category, message)); }
        static void info(long requestId, String category, String message) { enqueue(format("INFO", Long.toString(requestId), category, message)); }
        static void error(String category, String message, Throwable error) { enqueue(format("ERROR", "-", category, message + "\n" + stack(error))); }
        static void error(long requestId, String category, String message, Throwable error) { enqueue(format("ERROR", Long.toString(requestId), category, message + "\n" + stack(error))); }
        static String renderThreadDump(long requestId) {
            for (var entry : Thread.getAllStackTraces().entrySet()) {
                Thread thread = entry.getKey();
                if (!thread.getName().equals("Render thread")) continue;
                StringBuilder full = new StringBuilder("\"Render thread\" id=")
                        .append(thread.getId()).append(" state=").append(thread.getState());
                StringBuilder compact = new StringBuilder();
                StackTraceElement[] frames = entry.getValue();
                for (int index = 0; index < frames.length; index++) {
                    full.append("\n    at ").append(frames[index]);
                    if (index < 12) {
                        if (!compact.isEmpty()) compact.append(" <- ");
                        compact.append(frames[index].getClassName()).append('.').append(frames[index].getMethodName())
                                .append(':').append(frames[index].getLineNumber());
                    }
                }
                enqueue(format("ERROR", Long.toString(requestId), "RENDER-THREAD-DUMP", full.toString()));
                return compact.toString();
            }
            enqueue(format("ERROR", Long.toString(requestId), "RENDER-THREAD-DUMP", "Render thread was not found"));
            return "";
        }
        static void stop() { if (writer != null) QUEUE.offer(POISON); }

        private static String format(String level, String requestId, String category, String message) {
            return TIME.format(Instant.now()) + " [" + level + "] [thread=" + Thread.currentThread().getName() + "] [request=" + requestId + "] [" + category + "] " + message;
        }
        private static String stack(Throwable error) {
            StringWriter text = new StringWriter();
            error.printStackTrace(new PrintWriter(text));
            return text.toString();
        }
        private static void enqueue(String line) {
            if (!QUEUE.offer(line)) System.err.println("[Baritone Web Bridge] Debug log queue is full");
        }
        private static void writeLoop() {
            while (true) {
                try {
                    String line = QUEUE.take();
                    if (line == POISON) break;
                    if (file != null) {
                        if (Files.exists(file) && Files.size(file) > 8 * 1024 * 1024) {
                            Path previous = file.resolveSibling("baritone-web-bridge.previous.log");
                            Files.deleteIfExists(previous);
                            Files.move(file, previous);
                        }
                        Files.writeString(file, line + System.lineSeparator(), StandardCharsets.UTF_8, StandardOpenOption.CREATE, StandardOpenOption.APPEND);
                    }
                } catch (InterruptedException ignored) {
                    Thread.currentThread().interrupt();
                    break;
                } catch (IOException error) {
                    System.err.println("[Baritone Web Bridge] Log write failed: " + error.getMessage());
                }
            }
        }
    }
}
