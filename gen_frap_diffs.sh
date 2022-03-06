#!/bin/bash
# Script that generates `update_frap.sh`, which is meant to be used to update
# the fraps library from its old submodule version
# (https://github.com/achlipala/frap/tree/49a020a348cfd6dfc4d04f0bc1790e4b1aaa93b0)
# to a state that can be compiled with Coq version 8.11.0.

OUTPUT_NAME="update_frap.sh"

if [[ "$#" != "2" ]]; then
  echo "Usage: $0 original_folder update_folder" >&2
  exit 1
fi

ORIGINAL_FOLDER="$1"
UPDATED_FOLDER="$2"

if [[ -f "$OUTPUT_NAME" ]]; then
  echo "$OUTPUT_NAME already exists" >&2
  exit 1
fi

echo "#!/bin/bash" >"$OUTPUT_NAME"

for f in $(ls "$ORIGINAL_FOLDER"); do
  diffs=$(diff -e "$ORIGINAL_FOLDER/$f" "$UPDATED_FOLDER/$f" | base64 -w 0)
  if [[ "$diffs" != "" ]]; then
    echo "((echo '$diffs' | base64 -d) && echo w) | ed - 'frap/$f'" >>"$OUTPUT_NAME"
  fi
done

chmod +x "$OUTPUT_NAME"

