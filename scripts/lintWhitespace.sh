#!/bin/bash

if [ ! -d Batteries ]; then
    echo "Batteries directory not found; run this script from the repository root." >&2
    exit 1
fi

issues_found=0

while IFS= read -r -d '' file; do
    # Check for trailing whitespace and print line number if found
    while IFS=: read -r line_num line; do
        echo "Trailing whitespace found in $file at line $line_num: $line"
        issues_found=1
    done < <(grep -n "[[:blank:]]$" "$file")

    # Check if the last line ends with a new line
    if [ -s "$file" ] && [ "$(tail -c 1 "$file" | od -c | awk 'NR==1 {print $2}')" != "\n" ]; then
        echo "Last line does not end with a new line in: $file"
        issues_found=1
    fi
done < <(find Batteries -type f -name "*.lean" -print0)

exit "$issues_found"
