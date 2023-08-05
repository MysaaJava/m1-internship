BEGIN {
    b=1
}
/\\>\[2\]\\AgdaComment{--\\#}\\<%/ {
    b=2
}
/^\\\\\[\\AgdaEmptyExtraSkip\]%$/ {
    agg=agg""((agg=="")?"":"\n")""$0
    b=0    
}
/^%$/ {
    agg=agg""((agg=="")?"":"\n")""$0
    b=0
}
/^\\\\$/ {
    agg=agg""((agg=="")?"":"\n")""((b==2)?"":$0)
    b=0
}
/^\\>\[0\]\\<%$/ {
    agg=agg""((agg=="")?"":"\n")""$0
    b=0
}
// {
    if (b==1){
        if(agg!=""){
            print agg
        }
        agg=""
        print $0
    }else if (b==0){
        b=1
    }
}
