function getTheme() {
    return localStorage.getItem("theme") || "system";
}

function setTheme(themeName) {
    localStorage.setItem('theme', themeName);
    if (themeName == "system") {
        themeName = parent.matchMedia("(prefers-color-scheme: dark)").matches ? "dark" : "light";
    }
    // the navbar is in an iframe, so we need to set this variable in the parent document
    for (const win of [window, parent]) {
        win.document.documentElement.setAttribute('data-theme', themeName);
    }
}

setTheme(getTheme())

document.addEventListener("DOMContentLoaded", function() {
    document.querySelectorAll("#color-theme-switcher input").forEach((input) => {
        if (input.value == getTheme()) {
            input.checked = true;
        }
        input.addEventListener('change', e => setTheme(e.target.value));
    });

    // also check to see if the user changes their theme settings while the page is loaded.
    parent.matchMedia('(prefers-color-scheme: dark)').addEventListener('change', event => {
        setTheme(getTheme());
    })
});

// un-hide the colorscheme picker
document.querySelector("#settings").removeAttribute('hidden');
