#!/bin/bash

IDA='/path/to/your/idat64'

bin=$1
output_dir=$bin"_functions_refs"

# this command will prepare the database of this binary
#pre_cmd="$IDA -B $bin"
#echo $pre_cmd
#eval $pre_cmd

# run ida python script to collect functions info
cmd="$IDA -A -S\"./idapy/func_refs.py $output_dir\" $bin"
#echo $cmd
eval $cmd

