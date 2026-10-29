#!/usr/bin/env bash
# Watchdog for package (v) builds: logs the peak RSS (total and anonymous)
# of every `lean` process compiling a module under Sec8/D/N13/ and kills it
# when its anonymous RSS exceeds $LIMIT kB.
LIMIT=${LIMIT:-4500000}
LOG=${LOG:-$HOME/n13v-watch.log}
declare -A peak
while true; do
  for p in $(pgrep -x lean); do
    cmd=$(tr '\0' ' ' < /proc/$p/cmdline 2>/dev/null) || continue
    case "$cmd" in
      *Sec8/D/N13/*|*Sec8/D/W4/BoxHgLow*) ;;
      *) continue ;;
    esac
    read -r rss anon <<< "$(awk '/^VmRSS/{r=$2} /^RssAnon/{a=$2} END{print r, a}' /proc/$p/status 2>/dev/null)"
    [ -z "$anon" ] && continue
    mod=$(echo "$cmd" | grep -oE '(N13|W4)/[A-Za-z0-9_]*\.lean' | head -1)
    key="$p:$mod"
    if [ -z "${peak[$key]}" ] || [ "$anon" -gt "${peak[$key]}" ]; then
      peak[$key]=$anon
      echo "$(date +%H:%M:%S) peak $key anon=$anon rss=$rss" >> "$LOG"
    fi
    if [ "$anon" -gt "$LIMIT" ]; then
      echo "$(date +%H:%M:%S) KILL $key anon=$anon rss=$rss" >> "$LOG"
      kill "$p"
    fi
  done
  sleep 1
done
