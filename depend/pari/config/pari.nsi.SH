cfg=$config_dir
obj=$objdir
file="$obj/pari.nsi"
case "$sizeof_long" in
  4) bitsize=32;;
  8) bitsize=64;;
esac;

if [ -f "$cfg/$osname-pari.nsi" ]; then
  echo "Extracting $file"
  "$cfg/$osname-pari.nsi" $bitsize > "$file"
fi
