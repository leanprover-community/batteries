#!/bin/bash

tmpfile=$(mktemp)
issues_found=0

find Batteries -type f -name "*.lean" | while IFS= read -r file; do
    # Check for trailing whitespace and print line number if found
    while IFS=: read -r line_num line; do
        echo "Trailing whitespace found in $file at line $line_num: $line"
        echo 1 > "$tmpfile"
    done < <(grep -n "[[:blank:]]$" "$file")

    # Check if the last line ends with a new line
    if [ "$(tail -c 1 "$file" | od -c | awk 'NR==1 {print $2}')" != "\n" ]; then
        echo "Last line does not end with a new line in: $file"
        echo 1 > "$tmpfile"
    fi
done

if [ -f "$tmpfile" ]; then
    issues_found=$(<"$tmpfile")
fi
rm -f "$tmpfile"

exit $issues_found
