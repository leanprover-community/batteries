function expandNav() {
    // Get the current page URL without the suffix after #
    var currentPageURL = window.location.href.split('#')[0];

    // Get all anchor tags
    var as = document.querySelector('.navframe').contentWindow.document.body.querySelectorAll('a');
    for (const a of as) {
        if (a.href) {
            var href = a.href.split('#')[0];
            // find the one with the current url
            if (href === currentPageURL) {
                a.style.fontWeight = 'bold';
                a.style.color = 'inherit';
                // open all detail tags above the current
                var el = a.parentNode.closest('details');
                while (el) {
                    el.open = true;
                    el = el.parentNode.closest('details');
                }
                // center the link we were looking for and stop
                a.scrollIntoView({ behavior: 'instant', block: 'center' });
                break;
            }
        }
    }
}

var navFrame = document.querySelector('.navframe');
if (navFrame.contentDocument.readyState === "complete") {
    expandNav();
} else {
    navFrame.addEventListener('load', expandNav);
}
