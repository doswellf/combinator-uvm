<'

struct data {
    % addr:int;
    % trailer:int;
    % txt:string;
};

struct pdata {
    % data:int;
    % addr:uint(bits:4);
    % payload:int;
};

// Marks pdata is mapped to a SV packed struct
uvm_ml_packed_struct pdata;

'>