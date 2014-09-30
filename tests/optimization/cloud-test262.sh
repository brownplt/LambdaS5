#!/bin/bash
#
#$ -cwd
#
#
BASE="/home/lijunsong/github/LambdaS5/tests/"

get_usage () {
echo "to use this script, create an directory and put two files in it.
  1. config.txt, which has one line to specifies s5 optimization arguments;
  2. jslists.txt, which contains test262 js absolute file path.
  
  run qsub -t 1-100 cloud-test262.sh"
    
exit 1
}
get_filepath_list () {
    base=`pwd`
    jsfiles=`find $BASE/test262/test262/test/suite/ch* -name '*.js'`
    echo "$jsfiles"
}

get_filepath () {
    # the $1 is the index, $2 is the file
    cat $2 | sed -n "$1 p" 
}

################# functions above ###############

# config file: the file MUST contain one lines, which 
# specifies s5 arguments for optimization phases
configfilename=config.txt
listname=jslists.txt

config_dir=`pwd`
output_dir=$config_dir

configpath=$config_dir/$configfilename
listpath=$config_dir/$listname

[ ! -f $configfilename ] && echo "$configfilename is not found" && get_usage 
[ ! -f $listname ] && echo "$listpath is not found" && get_usage

# todo: wen running on grid, will anything significant var be defined?
fileindex=$SGE_TASK_ID
if [ -z $SGE_TASK_ID ]; then
    echo "debug mode"
    fileindex=2
fi    
filepath=`get_filepath $fileindex $listpath`

[ -z $filepath ] && echo "$filepath is empty" && exit 1




# get optimization command from file 
optargs=`cat $configpath | head -n 1`
[ -z "$optargs" ] && echo "opt args is empty" && exit 1

################## start running test ##################

# working directory is in tests/
cd $BASE
filename=$(basename $filepath)
#  NOTE: filename should contains .js. S8.4-A1
#  will test A1, A10, A11, A1*
chapter=`echo $filepath | grep -o 'ch[0-9][0-9]'`
[ -z $chapter ] && echo "chapter is empty" && exit 1
# start testing the strict mode

nonstrictdir=$output_dir/$chapter-nonstrict
mkdir -p $nonstrictdir
python test262/test262/tools/packaging/test262.py \
  --non_strict_only \
  --tests test262/test262/ \
  --command "optimization/test-js.sh {{path}} $nonstrictdir $optargs" \
  $filename > $nonstrictdir/$filename.nonstrict.result

# start testing the non-strict mode
strictdir=$output_dir/$chapter-strict
mkdir -p $strictdir
python test262/test262/tools/packaging/test262.py \
  --strict_only \
  --tests test262/test262/ \
  --command "optimization/test-js.sh {{path}} $strictdir $optargs" \
  $filename > $strictdir/$filename.strict.result
