TMP=$(mktemp -d); git clone https://github.com/coq-community/templates.git $TMP
$TMP/generate.sh
rm -rf $TMP
