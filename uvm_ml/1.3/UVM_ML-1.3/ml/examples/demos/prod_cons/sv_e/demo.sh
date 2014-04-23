#! /bin/tcsh -f

set script = `basename $0`
if ( ! ($?UVM_ML_HOME) ) then
   echo "Please set environment variable UVM_ML_HOME to the parent directory of ml";
   exit
endif

if ($#argv == 0) then
   echo "Usage: $script <IES | VCS | QUESTA> "
   exit 0
endif

while ($#argv > 0)
   switch ($1)
      case IES:
      case IES_NCSC:
        make ies
        breaksw
      case VCS :
        make vcs
        breaksw
      case QUESTA :
        make questa
        breaksw
      case -h :
      case -help:
      default:
         echo "Usage: $script <IES | VCS | QUESTA> "
         exit 0
   endsw
   shift
end

exit 0
