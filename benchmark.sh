#!/bin/bash

set -e  # Exit if make fails
make depend && make #&& make clean
set +e  # Do not exit if any subsequent command fails
clear

FLAGS=""

# Flag -a is set for testing all the Llama Program Suite
AFLAG=false

# Flags Usable by the compiler
VERFLAG=""
PFLAG=""
CFLAG=""
FFLAG=""
UFLAG=""
SFLAG=""
TFLAG=""
IFLAG=""

function enableopts () {
  while getopts ":acTVpfusi" optname
    do
      case "$optname" in
        "a")
          AFLAG=true
          ;;
        "c")
          CFLAG="-${optname}"
          ;;
        "T")
          TFLAG="-${optname}"
          ;;
        "V")
          VERFLAG="-${optname}"
          ;;
        "p")
          PFLAG="-${optname}"
          ;;
        "f")
          FFLAG="-${optname}"
          ;;
        "u")
          UFLAG="-${optname}"
          ;;
        "s")
          SFLAG="-${optname}"
          ;;
        "i")
          IFLAG="-${optname}"
          ;;
        "?")
          echo "Unknown option ${OPTARG}"
          ;;
        ":")
          echo "No argument value for option $OPTARG"
          ;;
        *)
          echo "Internal error while processing options"
          ;;
      esac
    done
  return $OPTIND
}

function runtests () {
  for file in "$@"
    do
       echo -e "\e[1;32m$ Testing ${file} ..\e[0m"
       if [ -e $file ]; then
          ./llamac ${FLAGS} ${file}  # Calling the compiler
       else
          echo "File ${file} does not exist!"
       fi
    done
}

enableopts "$@"
argstart=$?

# Concat all the flags to one string
FLAGS="${PFLAG} ${CFLAG} ${FFLAG} ${TFLAG} ${UFLAG} ${SFLAG} ${IFLAG} ${VERFLAG}"

if $AFLAG; then   #If flag -a is set then test all the Llama Program Suite
   echo -e "\e[1;34mRunning Full Llama Test Suite\e[0m"
   echo -e "\e[1;34m*****************************\e[0m"
   for file in tests/* # Folder of the Llama Program Suite
   do
      echo -e "\e[1;32m$ Testing ${file} ..\e[0m"
      ./llamac ${FLAGS} ${file}  # Calling the compiler
   done
else             #If flag -a is NOT set then test all the files provided as arguments
   runtests "${@:$argstart}"
fi
