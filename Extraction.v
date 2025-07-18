Require Import Vevm.Vm.
Require Extraction.

Set Extraction Output Directory ".".

Extraction "vm.ml" interpret_all.
