**Output of command `agda --profile=internal Biequiv-main.agda`:**

```
Total                            9,911,574ms              
Miscellaneous                        1,018ms              
Typing                             697,325ms (8,688,554ms)
Typing.CheckRHS                  4,451,690ms              
Typing.OccursCheck               1,604,140ms              
Typing.InstanceSearch            1,285,098ms              
Typing.TypeSig                     648,063ms              
Typing.CheckLHS                      1,344ms     (2,225ms)
Typing.CheckLHS.UnifyIndices           881ms              
Typing.With                             10ms              
Serialization                      354,629ms   (432,808ms)
Serialization.BuildInterface        76,222ms              
Serialization.Compress               1,005ms              
Serialization.BinaryEncode             781ms              
Serialization.Sort                     169ms              
DeadCode                               130ms   (306,170ms)
DeadCode.DeadCodeInstantiateFull   290,793ms              
DeadCode.DeadCodeReachable          15,246ms              
Positivity                         286,733ms              
ProjectionLikeness                  62,640ms              
Coverage                            51,205ms    (51,936ms)
Coverage.UnifyIndices                  730ms              
Termination                            115ms    (46,006ms)
Termination.RecCheck                45,875ms              
Termination.Compare                     12ms              
Parsing                                832ms    (19,186ms)
Parsing.OperatorsExpr               17,634ms              
Parsing.OperatorsPattern               719ms              
Scoping                              1,054ms    (11,904ms)
Scoping.InverseScopeLookup          10,849ms              
Deserialization                      2,548ms     (3,593ms)
Deserialization.Compaction           1,044ms              
Highlighting                           800ms              
Import                                 170ms              
Injectivity                             52ms
```
