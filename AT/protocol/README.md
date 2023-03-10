# Protocol model of the autonomous taxi system: RG and TTES

This is a model of the protocol among the RG and TTES component. 
The [OCRA](https://ocra.fbk.eu/) tool can be directly used for verification:

```
> ocra-win64.exe AT.oss
*** This is ocra 2.1.0 (compiled on Fri Jul  2 09:08:41 2021)
*** For more information on ocra see <https://ocra.fbk.eu>
*** For bug reports, or any comment, please send an email to <ocra@fbk.eu>.
*** Copyright (c) 2013, Fondazione Bruno Kessler

*** This version of ocra is linked to NuSMV 2.6.0.
*** For more information on NuSMV see <http://nusmv.fbk.eu>
*** or email to <nusmv-users@fbk.eu>.
*** Copyright (C) 2010-2021, Fondazione Bruno Kessler

*** This version of ocra is linked to the CUDD library version 2.4.1
*** Copyright (c) 1995-2004, Regents of the University of Colorado

*** This version of ocra is linked to the MiniSat SAT solver.
*** See http://minisat.se/MiniSat.html
*** Copyright (c) 2003-2006, Niklas Een, Niklas Sorensson
*** Copyright (c) 2007-2010, Niklas Sorensson

ocra >  ocra_check_refinement

Checking refinement of component: AutoTaxi
  Checking "CONTRACT C_AutoTaxi REFINEDBY rg.C_RG, ttes.C_TTES;"
    Checking the correct implementation of "C_AutoTaxi"... [OK]
    Checking the correct environment of "rg.C_RG"... [OK]
    Checking the correct environment of "ttes.C_TTES"... [OK]

Checking refinement of component: RG

Checking refinement of component: TTES

  Summary: everything is OK.
ocra >
```