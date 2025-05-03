**Output of command `agda --profile=internal Final-thms.agda`:**

```
Total                            9,894,629ms              
Miscellaneous                        1,212ms              
Typing                             708,572ms (8,655,378ms)
Typing.CheckRHS                  4,449,480ms              
Typing.OccursCheck               1,587,790ms              
Typing.InstanceSearch            1,266,339ms              
Typing.TypeSig                     638,442ms              
Typing.CheckLHS                      3,861ms     (4,742ms)
Typing.CheckLHS.UnifyIndices           881ms              
Typing.With                             10ms              
Serialization                      328,273ms   (405,936ms)
Serialization.BuildInterface        75,269ms              
Serialization.BinaryEncode           1,184ms              
Serialization.Compress               1,048ms              
Serialization.Sort                     159ms              
DeadCode                               118ms   (325,743ms)
DeadCode.DeadCodeInstantiateFull   310,714ms              
DeadCode.DeadCodeReachable          14,911ms              
Positivity                         307,033ms              
ProjectionLikeness                  73,281ms              
Coverage                            45,590ms    (46,296ms)
Coverage.UnifyIndices                  705ms              
Termination                            121ms    (42,350ms)
Termination.RecCheck                42,211ms              
Termination.Compare                     14ms              
Parsing                                824ms    (19,942ms)
Parsing.OperatorsExpr               18,314ms              
Parsing.OperatorsPattern               803ms              
Scoping                              1,063ms    (12,315ms)
Scoping.InverseScopeLookup          11,252ms              
Deserialization                      2,998ms     (4,085ms)
Deserialization.Compaction           1,086ms              
Highlighting                           745ms              
Import                                 264ms              
Injectivity                             47ms
```
