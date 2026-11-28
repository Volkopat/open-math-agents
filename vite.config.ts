import { defineConfig } from "vite";
import vinext from "vinext";
import { cloudflare } from "@cloudflare/vite-plugin";

export default defineConfig({
  // Fonts stay separate files, loaded only by pages whose text needs them: inlined, the small ones (under 4 KB, such
  // as app/fonts/*-hu.woff2) would add their base64 to the stylesheet every page waits for.
  build: { assetsInlineLimit: (file: string) => (file.endsWith(".woff2") ? false : undefined) },
  plugins: [
    // No Workers Cache adapter: with Workers Cache on, every request (static files and the internal render call included)
    // is billed. Pages are cached by worker/entry.ts in the Cache API instead, which is not billed.
    vinext(),
    cloudflare({
      viteEnvironment: {
        name: "rsc",
        childEnvironments: ["ssr"],
      },
    }),
  ],
});
