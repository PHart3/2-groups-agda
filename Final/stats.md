**Total time taken on macOS Sequoia 15.6 (with M1 chip and 16 GB of RAM):**

```
Total                            15,551,036ms               
Miscellaneous                         2,093ms               
Typing                              959,359ms (14,087,187ms)
Typing.CheckRHS                   6,251,529ms               
Typing.InstanceSearch             4,495,479ms               
Typing.OccursCheck                1,696,559ms               
Typing.TypeSig                      675,551ms               
Typing.CheckLHS                       6,096ms      (8,685ms)
Typing.CheckLHS.UnifyIndices          2,588ms               
Typing.With                              23ms               
Serialization                       380,522ms    (465,804ms)
Serialization.BuildInterface         81,797ms               
Serialization.Compress                1,645ms               
Serialization.BinaryEncode            1,542ms               
Serialization.Sort                      297ms               
DeadCode                                354ms    (379,829ms)
DeadCode.DeadCodeInstantiateFull    361,735ms               
DeadCode.DeadCodeReachable           17,739ms               
Positivity                          351,244ms               
ProjectionLikeness                   83,488ms               
Termination                             581ms     (57,922ms)
Termination.RecCheck                 57,321ms               
Termination.Graph                        11ms               
Coverage                             50,183ms     (51,109ms)
Coverage.UnifyIndices                   926ms               
Parsing                               1,293ms     (37,554ms)
Parsing.OperatorsExpr                34,909ms               
Parsing.OperatorsPattern              1,352ms               
Scoping                               1,945ms     (26,848ms)
Scoping.InverseScopeLookup           24,902ms               
Deserialization                       4,674ms      (6,365ms)
Deserialization.Compaction            1,691ms               
Highlighting                          1,229ms               
Import                                  297ms               
Injectivity                              69ms
```
