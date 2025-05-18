for i in $(find . -maxdepth 2 -name "*.o"); do
  readelf --syms ${i} >tmp.txt
  lcount=$(cat tmp.txt | grep -v .data | grep -v .bss | grep -v .note | grep -v '\$' | grep -v .text | wc -l)
  if [ $lcount -ne 5 ]; then
    #~/aarch64-objdump.sh -D ${i} --section=.text >tmp.txt
    #asmcnt=$(tail +8 tmp.txt | wc -l)
    #echo $i $asmcnt
    echo $i
  fi
done
