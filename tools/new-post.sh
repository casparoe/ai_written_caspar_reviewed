#!/usr/bin/env bash
#
# Scaffold a new post interactively, optionally from a pasted markdown draft.
#
# Asks for every front matter field this blog uses, reads the post body from
# the clipboard (pbpaste) or a file, rewrites the draft to match the blog's
# conventions, shows the result, and writes _posts/<date>-<slug>.md.
#
# Conventions built in:
#   - `how_written` is required (rendered as the "Note from Caspar" box).
#   - No `tags:` — this blog does not use them.
#   - A leading "# Title" heading becomes the front matter title.
#   - \( \) and \[ \] math delimiters become $$ (kramdown treats \( as an
#     escaped paren and would strip the backslash, breaking MathJax).
#   - ```svg fences are saved to assets/img/<prefix>-figN.svg and replaced by
#     an image reference with width/height from the viewBox; an italic line
#     after the fence is attached directly below the image as its caption.
#
# Usage: bash tools/new-post.sh

set -eu
set -o pipefail

repo_root=$(cd "$(dirname "$0")/.." && pwd)

help() {
  echo "Usage:"
  echo
  echo "   bash /path/to/new-post [options]"
  echo
  echo "Prompts for the post's front matter fields (title, slug, date,"
  echo "description, categories, math, pin, how_written — never tags) and"
  echo "for the body: copy a full markdown draft (LaTeX math and \`\`\`svg"
  echo "figures welcome), answer 'c' to read it from the clipboard, or give"
  echo "a file path, or 'n' for an empty scaffold. The draft is rewritten"
  echo "to the blog's conventions and saved as _posts/<date>-<slug>.md,"
  echo "with figures extracted to assets/img/."
  echo
  echo "Options:"
  echo "     -h, --help           Print this help information."
}

while (($#)); do
  case $1 in
  -h | --help)
    help
    exit 0
    ;;
  *)
    echo -e "> Unknown option: '$1'\n"
    help
    exit 1
    ;;
  esac
done

tmpdir=$(mktemp -d)
trap 'rm -rf "$tmpdir"' EXIT

trim() {
  printf '%s' "$1" | sed -e 's/^[[:space:]]*//' -e 's/[[:space:]]*$//'
}

# Prompt for one line; sets $ans to the trimmed reply, or $2 if the reply is empty.
ask() {
  local prompt="$1" default="${2-}"
  if [ -n "$default" ]; then
    prompt="$prompt [$default]"
  fi
  read -r -e -p "$prompt: " ans || {
    echo
    echo "> Aborted." >&2
    exit 1
  }
  ans=$(trim "$ans")
  if [ -z "$ans" ]; then
    ans="$default"
  fi
}

ask_required() {
  while :; do
    ask "$@"
    if [ -n "$ans" ]; then
      return
    fi
    echo "  This field is required."
  done
}

# Yes/no prompt; sets $ans to "true" or "false". $2 is the default reply.
ask_yes_no() {
  while :; do
    ask "$1" "$2"
    case $ans in
    y | Y | yes | Yes)
      ans=true
      return
      ;;
    n | N | no | No)
      ans=false
      return
      ;;
    *) echo "  Please answer y or n." ;;
    esac
  done
}

slugify() {
  printf '%s' "$1" \
    | LC_ALL=C tr '[:upper:]' '[:lower:]' \
    | LC_ALL=C sed -e "s/'//g" \
        -e 's/[^a-z0-9]/-/g' \
        -e 's/--*/-/g' \
        -e 's/^-*//' \
        -e 's/-*$//'
}

# Print $1 as a YAML scalar: as-is when plainly safe, single-quoted otherwise.
yaml_scalar() {
  local safe='^[A-Za-z0-9][A-Za-z0-9 .,()!?/&-]*$'
  if [[ $1 =~ $safe ]]; then
    printf '%s' "$1"
  else
    printf "'%s'" "$(printf '%s' "$1" | sed "s/'/''/g")"
  fi
}

# Print "<key>: >-" followed by $2 as an indented folded block scalar
# (newlines fold into spaces, and no character needs escaping).
yaml_folded() {
  printf '%s: >-\n' "$1"
  printf '%s\n' "$2" | sed 's/^/  /'
}

# True if $1 is a real YYYY-MM-DD date. Tries BSD date, then GNU date;
# comparing the round-trip catches rollovers like 2026-02-30.
valid_date() {
  local out
  out=$(date -j -f '%Y-%m-%d' "$1" '+%Y-%m-%d' 2>/dev/null) \
    || out=$(date -d "$1" '+%Y-%m-%d' 2>/dev/null) \
    || return 1
  [ "$out" = "$1" ]
}

echo "> New post — each field maps onto the front matter (this blog uses no tags)."
echo "> For a finished draft: copy the whole markdown to the clipboard first;"
echo "> title, math delimiters, and SVG figures are then handled automatically."
echo

body_raw="$tmpdir/body.raw"
body_out="$tmpdir/body.out"

body_mode=""
while [ -z "$body_mode" ]; do
  ask "Body — c = clipboard (pbpaste), n = none, or a markdown file path" "c"
  case $ans in
  c | clipboard)
    if ! command -v pbpaste >/dev/null 2>&1; then
      echo "  pbpaste not found — give a file path instead."
      continue
    fi
    pbpaste | tr -d '\r' >"$body_raw"
    if ! grep -q '[^[:space:]]' "$body_raw"; then
      echo "  Clipboard is empty — copy the post markdown first, then retry."
      continue
    fi
    body_mode="clipboard"
    ;;
  n | none)
    : >"$body_raw"
    body_mode="none"
    ;;
  *)
    src=$ans
    case $src in "~"*) src="$HOME${src#\~}" ;; esac
    if [ ! -f "$src" ]; then
      echo "  No such file: $src"
      continue
    fi
    tr -d '\r' <"$src" >"$body_raw"
    body_mode="file"
    ;;
  esac
done

title_default=""
body_lines=0
if [ "$body_mode" != "none" ]; then
  body_lines=$(wc -l <"$body_raw" | tr -d '[:space:]')
  echo "> Read $body_lines lines from $body_mode."
  first_line=$(sed -n '/[^[:space:]]/{p;q;}' "$body_raw")
  case $first_line in
  '# '*) title_default=$(trim "${first_line#"# "}") ;;
  esac
fi

if [ -n "$title_default" ]; then
  ask "Title" "$title_default"
  title="$ans"
else
  ask_required "Title"
  title="$ans"
fi

ask "Slug (filename and URL)" "$(slugify "$title")"
slug=$(slugify "$ans")
if [ -z "$slug" ]; then
  echo "> Slug is empty after sanitizing — try one with letters or digits." >&2
  exit 1
fi

date_re='^[0-9][0-9][0-9][0-9]-[0-9][0-9]-[0-9][0-9]$'
datetime_re='^[0-9][0-9][0-9][0-9]-[0-9][0-9]-[0-9][0-9] [0-9][0-9]:[0-9][0-9]:[0-9][0-9] [+-][0-9][0-9][0-9][0-9]$'
while :; do
  ask "Date (YYYY-MM-DD, or 'YYYY-MM-DD HH:MM:SS +0000')" "$(date +%Y-%m-%d)"
  if [[ $ans =~ $date_re ]] && valid_date "$ans"; then
    post_date="$ans"
    front_date="$ans 00:00:00 +0000"
    break
  elif [[ $ans =~ $datetime_re ]] && valid_date "${ans%% *}"; then
    post_date="${ans%% *}"
    front_date="$ans"
    break
  fi
  echo "  Not a valid date."
done

post_file="$repo_root/_posts/$post_date-$slug.md"
if [ -e "$post_file" ]; then
  echo "> _posts/$post_date-$slug.md already exists — not overwriting." >&2
  exit 1
fi

# Figure file prefix: only relevant when the draft contains ```svg fences.
fig_prefix="$slug"
fig_count=0
if [ "$body_mode" != "none" ]; then
  fig_count=$(grep -c '^```svg[[:space:]]*$' "$body_raw" || true)
fi
if [ "$fig_count" -gt 0 ]; then
  while :; do
    ask "Figure file prefix (files become <prefix>-figN.svg)" "$slug"
    fig_prefix=$(slugify "$ans")
    if [ -z "$fig_prefix" ]; then
      echo "  Empty after sanitizing — try again."
      continue
    fi
    clash=""
    i=1
    while [ "$i" -le "$fig_count" ]; do
      if [ -e "$repo_root/assets/img/$fig_prefix-fig$i.svg" ]; then
        clash="$fig_prefix-fig$i.svg"
        break
      fi
      i=$((i + 1))
    done
    if [ -z "$clash" ]; then
      break
    fi
    echo "  assets/img/$clash already exists — pick another prefix."
  done
fi

figs=0
inline_n=0
display_n=0
pipes_n=0
h1_stripped=0
fig_files=""
if [ "$body_mode" != "none" ]; then
  cat >"$tmpdir/transform.awk" <<'AWK_EOF'
# Transform a pasted markdown draft into blog-convention markdown.
# Input: raw body on stdin.
# Vars (via -v): prefix — figure file basename prefix; figdir — staging dir.
# Output: transformed body on stdout; figN.svg files and a stats file in figdir.

function out(s) { print s; last_blank = (s == "") }

# Replace | with \vert by string surgery: BSD awk and gawk disagree on
# backslash handling in gsub replacement text, so gsub cannot be used here.
function escape_pipes(s,   out, p) {
  out = ""
  while ((p = index(s, "|")) > 0) {
    out = out substr(s, 1, p - 1) "\\vert "
    s = substr(s, p + 1)
    nvert++
  }
  return out s
}

# Convert inline math \( .. \) to $$ .. $$. Pipes inside the span become
# \vert (the same LaTeX symbol): kramdown scans for tables at block level
# before it parses math spans, so a raw | inside inline math on the first
# line of a paragraph turns the whole paragraph into a table row.
function mathline(s,   res, ipos, after, cpos, inner, n) {
  res = ""
  while ((ipos = index(s, "\\(")) > 0) {
    after = substr(s, ipos + 2)
    cpos = index(after, "\\)")
    if (cpos == 0) break
    inner = escape_pipes(substr(after, 1, cpos - 1))
    res = res substr(s, 1, ipos - 1) "$$" inner "$$"
    s = substr(after, cpos + 2)
    in_open++; in_close++
  }
  # dangling delimiters (counted so the imbalance warning still fires)
  n = gsub(/\\\(/, "$$", s); in_open += n
  n = gsub(/\\\)/, "$$", s); in_close += n
  n = gsub(/\\\[/, "$$", s); stray += n
  n = gsub(/\\\]/, "$$", s); stray += n
  n = gsub(/\|/, "|", s); rawpipe += n
  return res s
}

function close_display() {
  out("$$")
  pending_blank = 1
  state = "normal"
}

function finish_figure(  fname, vb, a, k, ref) {
  fname = figdir "/fig" nfig ".svg"
  printf "%s", svgtext > fname
  close(fname)
  figw[nfig] = ""; figh[nfig] = ""
  if (match(svgtext, /viewBox[ \t]*=[ \t]*["'][^"']*["']/)) {
    vb = substr(svgtext, RSTART, RLENGTH)
    sub(/^viewBox[ \t]*=[ \t]*["']/, "", vb)
    sub(/["']$/, "", vb)
    k = split(vb, a, /[ \t,]+/)
    if (k >= 4) { figw[nfig] = a[3]; figh[nfig] = a[4] }
  }
  ref = "![Figure " nfig "](/assets/img/" prefix "-fig" nfig ".svg)"
  if (figw[nfig] != "" && figh[nfig] != "")
    ref = ref "{: width=\"" figw[nfig] "\" height=\"" figh[nfig] "\" }"
  if (!last_blank) out("")
  out(ref)
  state = "afterfig"
}

BEGIN { state = "normal"; last_blank = 1 }

{
  L = $0
  sub(/\r$/, "", L)

  # Take a leading "# Title" heading out of the body (it lives in front matter).
  if (!seen_content) {
    if (L ~ /^[ \t]*$/) next
    seen_content = 1
    if (L ~ /^# /) { had_h1 = 1; skipping = 1; next }
  }
  if (skipping) {
    if (L ~ /^[ \t]*$/) next
    skipping = 0
  }

  if (state == "svg") {
    if (L ~ /^```[ \t]*$/) finish_figure()
    else svgtext = svgtext L "\n"
    next
  }

  if (state == "fence") {
    out(L)
    if (L ~ /^```/) state = "normal"
    next
  }

  # Display math is printed verbatim: sequences like \\( inside \substack or
  # \\[2pt] line breaks must not be touched by the inline conversion.
  if (state == "display") {
    t = L
    sub(/[ \t]+$/, "", t)
    if (t ~ /^[ \t]*\\\]$/) { close_display(); next }
    if (t ~ /\\\]$/) {
      sub(/\\\]$/, "", t)
      sub(/[ \t]+$/, "", t)
      out(t)
      close_display()
      next
    }
    out(L)
    next
  }

  # Right after an extracted figure: swallow blank lines and attach a fully
  # italic line as the caption, directly below the image (theme convention).
  if (state == "afterfig") {
    if (L ~ /^[ \t]*$/) next
    state = "normal"
    if (L ~ /^\*[^*].*[^*]\*$/ || L ~ /^_[^_].*[^_]_$/) {
      figcap[nfig] = 1
      out(mathline(L))
      pending_blank = 1
      next
    }
    out("")
    # not a caption: fall through and treat L as a normal line
  }

  if (pending_blank) {
    if (L !~ /^[ \t]*$/) out("")
    pending_blank = 0
  }
  if (L ~ /^```svg[ \t]*$/) { nfig++; svgtext = ""; state = "svg"; next }
  if (L ~ /^```/) { out(L); state = "fence"; next }
  t = L
  sub(/^[ \t]+/, "", t)
  sub(/[ \t]+$/, "", t)
  # Kramdown wants display math as a standalone $$ block, blank-line-separated.
  if (t == "\\[") {
    if (!last_blank) out("")
    out("$$")
    ndisp++
    state = "display"
    next
  }
  if (t ~ /^\\\[.*\\\]$/) {
    inner = substr(t, 3, length(t) - 4)
    sub(/^[ \t]+/, "", inner)
    sub(/[ \t]+$/, "", inner)
    if (!last_blank) out("")
    out("$$")
    out(inner)
    out("$$")
    ndisp++
    pending_blank = 1
    next
  }
  out(mathline(L))
}

END {
  sfile = figdir "/stats"
  if (state == "svg" || state == "fence") print "error unclosed-code-fence" > sfile
  if (state == "display") print "error unclosed-display-math" > sfile
  print "h1 " (had_h1 ? 1 : 0) > sfile
  print "figs " (nfig + 0) > sfile
  for (i = 1; i <= nfig; i++)
    print "fig " i " " (figw[i] == "" ? "-" : figw[i]) " " (figh[i] == "" ? "-" : figh[i]) " " (figcap[i] ? 1 : 0) > sfile
  print "inline " (in_open + 0) > sfile
  print "display " (ndisp + 0) > sfile
  print "pipes " (nvert + 0) > sfile
  if (in_open != in_close) print "warn inline-math-imbalance opens=" in_open " closes=" in_close > sfile
  if (stray) print "warn stray-display-delimiters " (stray + 0) > sfile
  if (rawpipe) print "warn pipes-outside-math " (rawpipe + 0) " (kramdown may render those paragraphs as tables)" > sfile
  close(sfile)
}
AWK_EOF

  awk -v prefix="$fig_prefix" -v figdir="$tmpdir" -f "$tmpdir/transform.awk" \
    <"$body_raw" >"$body_out"

  echo
  echo "> Body transformations:"
  while read -r key a b c d; do
    case $key in
    error)
      echo "> Draft problem: $a — fix the pasted markdown and rerun." >&2
      exit 1
      ;;
    h1) h1_stripped=$a ;;
    figs) figs=$a ;;
    fig)
      dims="size unknown — add width/height by hand"
      if [ "$b" != "-" ] && [ "$c" != "-" ]; then dims="${b}x${c}"; fi
      cap="no caption line detected"
      if [ "$d" = "1" ]; then cap="caption attached"; fi
      echo "  - figure $a -> assets/img/$fig_prefix-fig$a.svg ($dims; $cap)"
      fig_files="$fig_files assets/img/$fig_prefix-fig$a.svg"
      ;;
    inline) inline_n=$a ;;
    display) display_n=$a ;;
    pipes) pipes_n=$a ;;
    warn) echo "  ! check the draft: $a $b $c $d" ;;
    esac
  done <"$tmpdir/stats"
  if [ "$h1_stripped" = "1" ]; then
    echo "  - leading '# ' heading removed from the body (title lives in front matter)"
  fi
  printf '  - math delimiters converted for kramdown: %s inline \\(..\\), %s display blocks\n' \
    "$inline_n" "$display_n"
  if [ "$pipes_n" -gt 0 ]; then
    printf '  - %s pipes inside inline math escaped as \\vert (kramdown table guard)\n' "$pipes_n"
  fi

  i=1
  while [ "$i" -le "$figs" ]; do
    if [ -e "$repo_root/assets/img/$fig_prefix-fig$i.svg" ]; then
      echo "> assets/img/$fig_prefix-fig$i.svg already exists — rerun with another prefix." >&2
      exit 1
    fi
    i=$((i + 1))
  done
  echo
fi

ask "Description (for previews/SEO; Enter to skip)"
description="$ans"

ask "Categories (comma-separated, at most 2 levels; Enter for none)"
categories_yaml=""
rest="$ans"
while [ -n "$rest" ]; do
  case $rest in
  *,*)
    item="${rest%%,*}"
    rest="${rest#*,}"
    ;;
  *)
    item="$rest"
    rest=""
    ;;
  esac
  item=$(trim "$item")
  if [ -n "$item" ]; then
    if [ -n "$categories_yaml" ]; then
      categories_yaml="$categories_yaml, "
    fi
    categories_yaml="$categories_yaml$(yaml_scalar "$item")"
  fi
done
if [ -n "$categories_yaml" ]; then
  categories_yaml="[$categories_yaml]"
fi

math_default=n
if [ "$body_mode" != "none" ] && grep -qF '$$' "$body_out"; then
  math_default=y
fi
ask_yes_no "Enable math (MathJax)? (y/n)" "$math_default"
math="$ans"

ask_yes_no "Pin to the top of the home page? (y/n)" "n"
pin="$ans"

echo
echo "how_written — the \"Note from Caspar\" box (markdown allowed)."
echo "Enter one or more lines; finish with an empty line."
how_written=""
while :; do
  read -r -e -p "> " line || {
    echo
    echo "> Aborted." >&2
    exit 1
  }
  line=$(trim "$line")
  if [ -z "$line" ]; then
    if [ -n "$how_written" ]; then
      break
    fi
    echo "  Required — every post explains how it was written."
    continue
  fi
  if [ -z "$how_written" ]; then
    how_written="$line"
  else
    how_written="$how_written
$line"
  fi
done

front_matter=$(
  echo '---'
  printf 'title: %s\n' "$(yaml_scalar "$title")"
  if [ -n "$description" ]; then
    yaml_folded description "$description"
  fi
  printf 'date: %s\n' "$front_date"
  if [ -n "$categories_yaml" ]; then
    printf 'categories: %s\n' "$categories_yaml"
  fi
  if $math; then
    echo 'math: true'
  fi
  if $pin; then
    echo 'pin: true'
  fi
  yaml_folded how_written "$how_written"
  echo '---'
)

echo
printf '%s\n' "$front_matter"
echo
if [ "$body_mode" = "none" ]; then
  echo "(empty body scaffold)"
else
  echo "(+ $(wc -l <"$body_out" | tr -d '[:space:]')-line body, $figs figure(s))"
fi
echo
ask_yes_no "Write to _posts/$post_date-$slug.md? (y/n)" "y"
if ! $ans; then
  echo "> Nothing written."
  exit 0
fi

printf '%s\n\n' "$front_matter" >"$post_file"
if [ "$body_mode" != "none" ]; then
  cat "$body_out" >>"$post_file"
fi

i=1
while [ "$i" -le "$figs" ]; do
  mv "$tmpdir/fig$i.svg" "$repo_root/assets/img/$fig_prefix-fig$i.svg"
  i=$((i + 1))
done

site_url=$(grep '^url:' "$repo_root/_config.yml" | head -n 1 | sed 's/^url:[[:space:]]*//' | tr -d "\"'" || true)
base_url=$(grep '^baseurl:' "$repo_root/_config.yml" | head -n 1 | sed 's/^baseurl:[[:space:]]*//' | tr -d "\"'" || true)

echo "> Created _posts/$post_date-$slug.md"
if [ "$figs" -gt 0 ]; then
  echo "> Created$fig_files"
fi
echo
echo "Next steps:"
if [ "$body_mode" = "none" ]; then
  echo "  1. Write the body below the front matter. Figures: save files under"
  echo "     assets/img/ and reference them as /assets/img/<name> (never inline"
  echo "     SVG); the caption is an italic line right after the image."
else
  echo "  1. Review the body — especially figure alt texts (placeholders now)"
  echo "     and any '!' warnings above."
fi
echo "  2. Publish: commit and push to main — GitHub Actions builds and deploys."
echo "     git add _posts/$post_date-$slug.md$fig_files"
echo "  3. Verify live (Pages caches ~10 min, so cache-bust):"
echo "     curl -s '$site_url$base_url/posts/$slug/?v=1' | grep -o '<title>[^<]*'"

if [ -t 0 ] && [ -n "${EDITOR:-}" ]; then
  ask_yes_no "Open in \$EDITOR ($EDITOR)? (y/n)" "n"
  if $ans; then
    $EDITOR "$post_file"
  fi
fi
