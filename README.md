# TFT-Verify

Using Ivy, Coq and Z3 to automatically verify the TFT protocol.

To verify safety, run:

`ivy_check diagnose=true tft_safety.ivy`

Coq proof is in Coq/TFT.v.

To verify finite-state liveness, run 
`python liveness/bmc.py [NUM_PEERS]`

where NUM_PEERS stands for the number of peers for BMC.
