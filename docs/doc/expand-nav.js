document.querySelector('.navframe').addEventListener('load', function() {
    // Get the current page URL without the suffix after #
    var currentPageURL = window.location.href.split('#')[0];

    // Get all anchor tags
    var as = document.querySelector('.navframe').contentWindow.document.body.querySelectorAll('a');
    for (const a of as) {
        if (a.href) {
            var href = a.href.split('#')[0];
            // find the one with the current url
            if (href === currentPageURL) {
                a.style.fontStyle = 'italic';
                // open all detail tags above the current
                var el = a.parentNode.closest('details');
                while (el) {
                    el.open = true;
                    el = el.parentNode.closest('details');
                }
                // seeing as we found the link we were looking for, stop
                break;
            }
        }
    }
});
