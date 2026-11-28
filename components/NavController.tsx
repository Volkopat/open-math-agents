"use client";
import { useEffect } from "react";
import { usePathname } from "next/navigation";

/** Makes the header's <details> menus behave like menus: one open at a time, closed by a click
 * outside, by Escape, by choosing a link, and after every navigation. Without JS they still open. */
export default function NavController() {
  const pathname = usePathname();
  useEffect(() => {
    const menus = () => Array.from(document.querySelectorAll<HTMLDetailsElement>("nav.nav details.drop"));
    const closeAll = (except?: Element | null) => menus().forEach((d) => { if (d !== except) d.open = false; });
    const onToggle = (e: Event) => { const d = e.target as HTMLDetailsElement; if (d.open) closeAll(d); };
    const onClick = (e: MouseEvent) => {
      const t = e.target as Element;
      const inside = t.closest("nav.nav details.drop");
      if (!inside) closeAll();
      else if (t.closest(".menu a")) closeAll();
    };
    const onKey = (e: KeyboardEvent) => { if (e.key === "Escape") closeAll(); };
    menus().forEach((d) => d.addEventListener("toggle", onToggle));
    document.addEventListener("click", onClick);
    document.addEventListener("keydown", onKey);
    return () => {
      menus().forEach((d) => d.removeEventListener("toggle", onToggle));
      document.removeEventListener("click", onClick);
      document.removeEventListener("keydown", onKey);
    };
  }, []);
  // close everything after each client-side navigation
  // ... and mark where you are: the link of the current page gets aria-current, its menu's label is highlighted.
  useEffect(() => {
    document.querySelectorAll<HTMLDetailsElement>("nav.nav details.drop").forEach((d) => (d.open = false));
    const here = (href: string | null) => {
      if (!href || href.startsWith("http") || href.includes("#")) return false;
      return href === pathname || (href !== "/" && pathname.startsWith(href + "/") && !["/papers"].includes(href));
    };
    document.querySelectorAll<HTMLAnchorElement>("nav.nav a").forEach((a) => {
      if (here(a.getAttribute("href"))) a.setAttribute("aria-current", "page"); else a.removeAttribute("aria-current");
    });
    document.querySelectorAll<HTMLDetailsElement>("nav.nav details.desk-menu").forEach((d) => {
      d.classList.toggle("current", Boolean(d.querySelector('a[aria-current="page"]')));
    });
  }, [pathname]);
  return null;
}
