#include "systemc.h"
#include <iostream>

int sc_main(int argc, char *argv[]) { 
#if (SYSTEMC_VERSION >= 20120701)
    std::cout << "2.3" << std::endl;
#else
    std::cout << "2.2" << std::endl;
#endif
    return 0 ;
}
