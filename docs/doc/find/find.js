/**
 * This module is used for the `/find` endpoint.
 *
 * Two basic kinds of search syntax are supported:
 *
 * 1. Query-Fragment syntax: `/find?pattern=Nat.add#doc` for documentation and `/find?pattern=Nat.add#src` for source code.
 * 2. Fragment-Only syntax:`/find/#doc/Nat.add` for documentation and `/find/#src/Nat.add` for source code.
 *
 * Though both of them are valid, the first one is highly recommended, and the second one is for compatibility and taste.
 *
 * There are some extended usage for the QF syntax. For example, appending `strict=false` to the query part
 * (`/find?pattern=Nat.add&strict=false#doc`) will allow you to use the fuzzy search, rather than strict match.
 * Also, the fragment is extensible as well. For now only `#doc` and `#src` are implement, and the plain query without
 * hash (`/find?pattern=Nat.add`) is used for computer-friendly data (semantic web is great! :P), while all other fragments
 * fallback to the `#doc` view.
 */

import { DeclarationDataCenter } from "../declaration-data.js";

function leanFriendlyRegExp(c) {
  try {
    return new RegExp("(?<!«[^»]*)" + c);
  } catch (e) {
    if (e instanceof SyntaxError) {
      // Lookbehind is not implemented yet in WebKit: https://bugs.webkit.org/show_bug.cgi?id=174931
      // Fall back to less friendly regex.
      return new RegExp(c);
    }
    throw e;
  }
}

/**
 * We don't use browser's default hash and searchParams in case Lean declaration name
 * can be like `«#»`, rather we manually handle the `window.location.href` with regex.
 */
const LEAN_FRIENDLY_URL_REGEX = /^[^?#]+(?:\?((?:[^«#»]|«.*»)*))?(?:#(.*))?$/;
const LEAN_FRIENDLY_AND_SEPARATOR = leanFriendlyRegExp("&");
const LEAN_FRIENDLY_EQUAL_SEPARATOR = leanFriendlyRegExp("=");
const LEAN_FRIENDLY_SLASH_SEPARATOR = leanFriendlyRegExp("/");

const [_, query, fragment] = LEAN_FRIENDLY_URL_REGEX.exec(window.location.href);
const queryParams = new Map(
  query
    ?.split(LEAN_FRIENDLY_AND_SEPARATOR)
    ?.map((p) => p.split(LEAN_FRIENDLY_EQUAL_SEPARATOR))
    ?.filter((l) => l.length == 2 && l[0].length > 0)
);
const fragmentPaths = fragment?.split(LEAN_FRIENDLY_SLASH_SEPARATOR) ?? [];

const encodedPattern = queryParams.get("pattern") ?? fragmentPaths[1]; // if first fail then second, may be undefined
const pattern = encodedPattern && decodeURIComponent(encodedPattern);
const strict = (queryParams.get("strict") ?? "true") === "true"; // default to true
const view = fragmentPaths[0];

findAndRedirect(pattern, strict, view);

/**
 * Find the result and redirect to the result page.
 * @param {string} pattern the pattern to search for
 * @param {string} view the view of the find result (`"doc"` or `"src"` for now)
 */
async function findAndRedirect(pattern, strict, view) {
  // if no pattern provided, directly redirect to the 404 page
  if (!pattern) {
    window.location.replace(`${SITE_ROOT}404.html`);
  }
  // search for result
  try {
    const dataCenter = await DeclarationDataCenter.init();
    let result = (dataCenter.search(pattern, strict) ?? [])[0]; // in case return non array
    // if no result found, redirect to the 404 page
    if (!result) {
      // TODO: better url semantic for 404, current implementation will lead to duplicate search for fuzzy match if not found.
      window.location.replace(`${SITE_ROOT}404.html#${pattern ?? ""}`);
    } else {
      result.docLink = SITE_ROOT + result.docLink;
      // success, redirect to doc or source page, or to the semantic rdf.
      if (!view) {
        window.location.replace(result.link);
      } else if (view == "doc") {
        window.location.replace(result.docLink);
      } else if (view == "src") {
        const [module, decl] = result.docLink.split("#", 2);
        window.location.replace(`${module}?jump=src#${decl}`);
      } else {
        // fallback to doc page
        window.location.replace(result.docLink);
      }
    }
  } catch (e) {
    document.write(`Cannot fetch data, please check your network connection.\n${e}`);
  }
}
