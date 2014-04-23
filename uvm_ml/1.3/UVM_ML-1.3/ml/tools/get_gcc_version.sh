#!/bin/csh -f 
$1 --version | grep -E '[0-9]+\.[0-9]+\.[0-9]+( |$)' -o | grep -E '[0-9]+\.[0-9]+' -o
