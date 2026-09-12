document.addEventListener("DOMContentLoaded", () => {
  const hash = document.location.hash.substring(1);
  const tgt = new URLSearchParams(document.location.search).get("jump");
  if (tgt === "src" && hash) {
    const target = document.getElementById(hash)
      ?.querySelector(".gh_link a")
      ?.getAttribute("href");
    if (target) window.location.replace(target);
  }
})
