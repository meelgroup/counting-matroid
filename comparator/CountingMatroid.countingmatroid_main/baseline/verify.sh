#!/bin/sh
set -eu
if [ "$(uname -s)" != Linux ]; then
  echo 'Comparator verification requires Linux and a working Landrun sandbox.' >&2
  exit 1
fi
if [ "$(id -u)" = 0 ]; then
  echo 'Run Comparator as an unprivileged user.' >&2
  exit 1
fi
checker="${1:-comparator}"
cd "$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)"
exec systemd-run --property=RestrictAddressFamilies=~AF_UNIX --user --pty \
  -E PATH="$PATH" \
  -E COMPARATOR_LANDRUN="${COMPARATOR_LANDRUN:-landrun}" \
  -E COMPARATOR_LEAN4EXPORT="${COMPARATOR_LEAN4EXPORT:-lean4export}" \
  --working-directory "$PWD" -- lake env "$checker" comparator.json
