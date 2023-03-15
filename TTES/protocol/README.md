# Protocol model of the autonomous taxi system: TTES by induction

This is a model to prove the correct implementation of the TTES protocol by induction. File induction0.oss is used to check the base case, and file inductionn.oss is used to check the induction argument. 
The [OCRA](https://ocra.fbk.eu/) tool can be directly used for verification:

```
$ ocra-win64.exe induction0.oss
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

ocra > ocra_check_refinement
Warning: in the refinement of component TTES0 the following ports are not connected:
output port trj_d

Checking refinement of component: TTES0
  Checking "CONTRACT C_TTES REFINEDBY tg.C_TG, tes.C_TES, vee.C_VEE;"
    Checking the correct implementation of "C_TTES"... [OK]
    Checking the correct environment of "tg.C_TG"... [OK]
    Checking the correct environment of "tes.C_TES"... [OK]
    Checking the correct environment of "vee.C_VEE"... [OK]

Checking refinement of component: TG

Checking refinement of component: TES

Checking refinement of component: VEE

  Summary: everything is OK.
ocra >
```

```
$ ocra-win64.exe inductionn.oss
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

ocra > ocra_check_refinement

Checking refinement of component: TTESN_plus_one
  Checking "CONTRACT C_TTES REFINEDBY tg.C_TG, ttesn.C_TTES, vee.C_VEE;"
    Checking the correct implementation of "C_TTES"... [OK]
    Checking the correct environment of "tg.C_TG"... [OK]
    Checking the correct environment of "ttesn.C_TTES"... [OK]
    Checking the correct environment of "vee.C_VEE"... [OK]

Checking refinement of component: TG

Checking refinement of component: TTESN

Checking refinement of component: VEE

  Summary: everything is OK.
ocra >
```
