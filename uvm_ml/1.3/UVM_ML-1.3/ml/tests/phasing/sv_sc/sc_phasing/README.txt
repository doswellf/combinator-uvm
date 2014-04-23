
test: 
        This test demonstrates phasing synchronization between UVM-SV and UVM-SC

environment: 
	IES: Native IES SV working with NC SystemC + UVM-SC
	IES_OSCI: Native IES SV working with UVM-SC + modified OSCI
	VCS: Native VCS SV working with UVM-SC + modified OSCI
	QUESTA: Native QUESTA SV working with UVM-SC + modified OSCI

to run: Make sure to source ml/setup.sh once before running any of the tests
	% make ies
        or
	% make ies_osci_proc
        or
        % make vcs
        or
        % make questa