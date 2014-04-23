#! /bin/bash
#
## 
## -------------------------------------------------------------
##    Copyright 2013 Cadence.
##    All Rights Reserved Worldwide
## 
##    Licensed under the Apache License, Version 2.0 (the
##    "License"); you may not use this file except in
##    compliance with the License.  You may obtain a copy of
##    the License at
## 
##        http://www.apache.org/licenses/LICENSE-2.0
## 
##    Unless required by applicable law or agreed to in
##    writing, software distributed under the License is
##    distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
##    CONDITIONS OF ANY KIND, either express or implied.  See
##    the License for the specific language governing
##    permissions and limitations under the License.
## -------------------------------------------------------------
## 

clean_in_between=""
to_stop=0
run_64bit=0
run_32bit=0
run_specman=0
only_specman=0
stub_out=""
log_base="irun"
tests_to_run=""
running_counter=0
passing_counter=0
failing_counter=0
failing_tests=""

for parameter in $*
do 
    if [ "$parameter" == "--clean" ]; then
        clean_in_between="clean"
    elif [ "parameter" == "--noclean" ]; then
        clean_in_between=""
    elif [ "$parameter" == "--stop" ]; then
        to_stop=1
    elif [ "$parameter" == "--nostop" ]; then
        to_stop=0
    elif [ "$parameter" == "--64bit" ]; then
        run_64bit=1
    elif [ "$parameter" == "--32bit" ]; then
        run_32bit=1
    elif [ "$parameter" == "--with-specman" ]; then
        run_specman=1
    elif [ "$parameter" == "--only-specman" ]; then
        run_specman=1;
        only_specman=1;
    elif [ "$parameter" == "--dry-run" ]; then
        stub_out="echo"
    elif [ "$parameter" == "--no-osci" ]; then
        /bin/true
    elif [ "$parameter" == "--no-ncsc" ]; then
       /bin/true
    else 
        tests_to_run="$tests_to_run $parameter"
    fi
done


if [ $run_64bit -eq 0 -a $run_32bit -eq 0 ]; then
    run_64bit=1
fi

if [ "$tests_to_run" == "" ]; then
    tests_to_run="ies vcs questa" 
fi

#if [ $run_64bit -eq 1 ]; then
#    bit_flag=""
#else
#    bit_flag='BITS=32'
#fi
   
for test_dir in */*/* ../examples/demos/*/*
do
    if [ -d $test_dir ]
    then
        number_of_e_files=$(ls -1 $test_dir/*.e 2>/dev/null | wc -l)
	if [ \( ! -e $test_dir/skip_test \)  -a \( \( $number_of_e_files -ge 1 \) -a \( \( $run_specman -eq 1 \) -o \( $only_specman -eq 1 \) \) -o \( \( $number_of_e_files -eq 0 \) \)  -a \( $only_specman -eq 0 \) \) ]; then
            pushd $test_dir
            for test in $tests_to_run
            do
                # 64 bit 
                if [ $run_64bit -eq 1 ]; then
                    running_counter=`expr $running_counter + 1`
                    bit_flag=""
                    #export UVM_ML_OVERRIDE=${UVM_ML_HOME}/ml/libs/backplane/${UVM_ML_COMPILER_VERSION}/64bit/
                    #export UNILANG_OVERRIDE=${UVM_ML_OVERRIDE}
                    $stub_out make $clean_in_between $test $bit_flag
                    # Check the status here
                    if [ $? -gt 0 ]; then 
                        failing_counter=`expr $failing_counter + 1`
                        failing_tests="$failing_tests $test_dir"
                        if [ $to_stop -eq 1 ]; then
                            exit 
                        fi
                    else
                        passing_counter=`expr $passing_counter + 1`
                    fi
                fi
                
                # 32 bit 
                if [ $run_32bit -eq 1 ]; then
                    running_counter=`expr $running_counter + 1`
                    bit_flag='BITS=32'
                    #export UVM_ML_OVERRIDE=${UVM_ML_HOME}/ml/libs/backplane/${UVM_ML_COMPILER_VERSION}/
                    #export UNILANG_OVERRIDE=${UVM_ML_OVERRIDE}
	            $stub_out make $clean_in_between $test $bit_flag
                    if [ $? -gt 0 ]; then 
                        failing_counter=`expr $failing_counter + 1`
                        failing_tests="$failing_tests $test_dir"
                        if [ $to_stop -eq 1 ]; then
                            exit 
                        fi
                    else
                        passing_counter=`expr $passing_counter + 1`
                    fi
                fi

            done
            if [ $run_32bit -eq 1 ]; then
                $stub_out make clean BITS=32
            fi
            if [ $run_64bit -eq 1 ]; then
                $stub_out make clean
            fi
	    popd
	fi
    fi
done

echo "**** $running_counter tests run *****" 
echo "**** $passing_counter tests passed ****"
echo "**** $failing_counter tests failed ****"
if [ $failing_counter -gt 0 ]; then
    echo FAILURE SUMMARY
    for failing_test in $failing_tests; do
        echo $failing_test
    done
fi
    
