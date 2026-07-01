/**
 * This module implements the `howabout` functionality in the 404 page.
 */

import { DeclarationDataCenter } from "./declaration-data.js";

const HOW_ABOUT = document.querySelector("#howabout");

// Show url of the missing page
if (HOW_ABOUT) {
  HOW_ABOUT.parentNode
    .insertBefore(document.createElement("pre"), HOW_ABOUT)
    .appendChild(document.createElement("code")).innerText =
    window.location.href.replace(/[/]/g, "/\u200b");

  // TODO: add how about functionality for similar page as well.
  const pattern = window.location.hash.replace("#", "");

  // try to search for similar declarations
  if (pattern) {
    HOW_ABOUT.innerText = "Please wait a second. I'll try to help you.";
    DeclarationDataCenter.init().then((dataCenter) => {
      let results = dataCenter.search(pattern, false);
      if (results.length > 0) {
        HOW_ABOUT.innerText = "How about one of these instead:";
        const ul = HOW_ABOUT.appendChild(document.createElement("ul"));
        for (const { name, docLink } of results) {
          const li = ul.appendChild(document.createElement("li"));
          const a = li.appendChild(document.createElement("a"));
          a.href = docLink;
          a.appendChild(document.createElement("code")).innerText = name;
        }
      } else {
        HOW_ABOUT.innerText =
          "Sorry, I cannot find any similar declarations. Check the link or use the module navigation to find what you want :P";
      }
    });
  }
}
