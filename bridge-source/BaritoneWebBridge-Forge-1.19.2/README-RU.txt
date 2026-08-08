Baritone Web Bridge — порт Fabric -> Forge 1.19.2
=================================================

Что уже перенесено
------------------
1. Fabric ClientModInitializer -> Forge @Mod конструктор.
2. FabricLoader пути -> FMLPaths.GAMEDIR / FMLPaths.CONFIGDIR.
3. FabricLoader чтение версий -> Forge ModList.
4. Yarn MinecraftClient -> Mojmap Minecraft.
5. Yarn ScreenHandler -> Mojmap AbstractContainerMenu.
6. Yarn SlotActionType -> Mojmap ClickType.
7. interactionManager.clickSlot -> gameMode.handleInventoryMouseClick.
8. Registries.ITEM.getId -> Registry.ITEM.getKey.
9. Yarn inventory/item/screen getters -> Mojmap эквиваленты.
10. Thread.threadId() -> Thread.getId(), чтобы исходник нормально собирался с Java 17.

HTTP часть и логика Baritone почти не менялись:
- com.sun.net.httpserver.* — обычный Java API;
- java.nio / executors / JSON parsing — обычный Java код;
- обращения к baritone.api.* сделаны через reflection, поэтому Baritone не нужен для compileJava.

ВАЖНО ПРО BARITONE
------------------
Для интеграции нужен Forge API-вариант Baritone под Minecraft 1.19.2.
Официальная ветка Baritone 1.19.2 указывает mod_version=1.9.4 (исторически Forge 43.1.65).
Не используй standalone-вариант, если он обфусцирует публичные имена API: мост ищет
baritone.api.BaritoneAPI, baritone.api.event.events.ChatEvent и
baritone.api.utils.BlockOptionalMeta по именам через reflection.

Как собрать
-----------
Самый надежный вариант:
1. Скачай официальный Forge MDK для Minecraft 1.19.2 / Forge 43.5.0.
2. Распакуй MDK.
3. Перенеси из этой папки src/ поверх src/ MDK.
4. Можно использовать приложенные build.gradle/settings.gradle как основу либо оставить MDK build.gradle
   и только убедиться, что dependency Minecraft Forge = 1.19.2-43.5.0 и mappings = official 1.19.2.
5. JDK 17.
6. Windows: gradlew.bat build
   Linux/macOS: ./gradlew build
7. JAR будет в build/libs/.

Что проверить, если компилятор ругается
---------------------------------------
Порт рассчитан на official/Mojang mappings Forge 1.19.2. Если твой проект использует Parchment
или старые MCP mappings, имена могут отличаться. В таком случае пришли ошибки compileJava — по ним
можно точно подогнать 2-3 оставшихся имени.

Mod ID сейчас: baritonewebbridge
Если в старом fabric.mod.json был другой id, поменяй одинаково:
- MOD_ID в BaritoneWebBridge.java
- modId в mods.toml
- имя секции dependencies.<modid> в mods.toml
