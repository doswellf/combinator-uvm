#!/bin/sh
mkdir -p uvm_sv_proj
mkdir -p ../html_docs/uvm_sv_adapter
NaturalDocs -i uvm_sv_adapter -o HTML ../html_docs/uvm_sv_adapter -p uvm_sv_proj
