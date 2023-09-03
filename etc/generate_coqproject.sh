## List tracked .v files
if [ -e .git ]; then
  TRACKED_V_FILES="$(git ls-files "*.v")"
else
  # This is expected when building using dune, so don't print the warning in that case:
  if [ "$GENERATE_COQPROJECT_FOR_DUNE" != "true" ]; then
    echo "Warning: Not a git clone, using find instead" >&2
  fi
  TRACKED_V_FILES="$(find theories contrib test -type f -name "*.v")"
fi

## List untracked .v files
#UNTRACKED_V_FILES=$(git ls-files --others --exclude-standard "*.v") 

## Combine untracked and tracked .v files
printf -v UNSORTED_V_FILES '%s\n%s' "$TRACKED_V_FILES" "$UNTRACKED_V_FILES"

## Sort combined .v files
SORTED_V_FILES=$(echo "$UNSORTED_V_FILES" | sort)

## _CoqProject header
COQPROJECT_HEADER=\
"###############################################################################
# WARNING: This file is autogenerated by the generate_coqproject.sh script
# found in etc/. It is set to be untracked by git.
###############################################################################
-R theories HoTT
-Q contrib HoTT.Contrib
-Q test HoTT.Tests

-arg -noinit
-arg -indices-matter
-arg -native-compiler -arg no
"

## Add additional lines when building with dune
if [ "$GENERATE_COQPROJECT_FOR_DUNE" == "true" ]; then
  COQPROJECT_HEADER="$COQPROJECT_HEADER
# Dune compatibility
-R _build/default/theories HoTT
-Q _build/default/contrib HoTT.Contrib
-Q _build/default/test HoTT.Tests
"
fi

## Store new _CoqProject in a variable
printf -v NEW_COQPROJECT '%s\n%s' "$COQPROJECT_HEADER" "$SORTED_V_FILES"

## Look for exisitng _CoqProject
if test -f "_CoqProject"; then
  OLD_COQPROJECT=$(cat _CoqProject)
  ## If it is the same don't overwrite
  if [ "$NEW_COQPROJECT" == "$OLD_COQPROJECT" ]; then
    exit 0
  fi
fi

## Overwrite _CoqProject
echo "$NEW_COQPROJECT" > _CoqProject
