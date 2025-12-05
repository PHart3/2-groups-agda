**Output of command `agda --profile=internal Final-thms.agda`:**

```
Total                            15,299,502ms               
Miscellaneous                         2,083ms               
Typing                              955,174ms (13,875,735ms)
Typing.CheckRHS                   6,153,951ms               
Typing.InstanceSearch             4,423,496ms               
Typing.OccursCheck                1,660,288ms               
Typing.TypeSig                      674,732ms               
Typing.CheckLHS                       5,577ms      (8,069ms)
Typing.CheckLHS.UnifyIndices          2,492ms               
Typing.With                              22ms               
Serialization                       371,062ms    (454,780ms)
Serialization.BuildInterface         80,221ms               
Serialization.Compress                1,607ms               
Serialization.BinaryEncode            1,244ms               
Serialization.Sort                      644ms               
DeadCode                                280ms    (391,726ms)
DeadCode.DeadCodeInstantiateFull    373,377ms               
DeadCode.DeadCodeReachable           18,068ms               
Positivity                          336,587ms               
ProjectionLikeness                   65,638ms               
Coverage                             52,708ms     (53,644ms)
Coverage.UnifyIndices                   935ms               
Termination                             404ms     (48,305ms)
Termination.RecCheck                 47,888ms               
Parsing                               1,192ms     (35,431ms)
Parsing.OperatorsExpr                32,920ms               
Parsing.OperatorsPattern              1,319ms               
Scoping                               1,792ms     (25,921ms)
Scoping.InverseScopeLookup           24,129ms               
Deserialization                       6,480ms      (8,153ms)
Deserialization.Compaction            1,672ms               
Highlighting                          1,145ms               
Import                                  293ms               
Injectivity                              67ms
```
