**Total time taken on macOS Sequoia 15.6 (with M1 chip and 16 GB of RAM):**

```
Total                            16,097,086ms               
Miscellaneous                         2,299ms               
Typing                            1,015,266ms (14,565,121ms)
Typing.CheckRHS                   6,443,143ms               
Typing.InstanceSearch             4,680,463ms               
Typing.OccursCheck                1,735,640ms               
Typing.TypeSig                      682,754ms               
Typing.CheckLHS                       6,693ms      (7,829ms)
Typing.CheckLHS.UnifyIndices          1,136ms               
Typing.With                              23ms               
Serialization                       409,567ms    (496,751ms)
Serialization.BuildInterface         83,904ms               
Serialization.Compress                1,656ms               
Serialization.BinaryEncode            1,317ms               
Serialization.Sort                      305ms               
Positivity                          391,706ms               
DeadCode                                508ms    (376,434ms)
DeadCode.DeadCodeInstantiateFull    355,145ms               
DeadCode.DeadCodeReachable           20,779ms               
ProjectionLikeness                   85,717ms               
Coverage                             53,355ms     (54,291ms)
Coverage.UnifyIndices                   935ms               
Termination                             335ms     (52,281ms)
Termination.RecCheck                 51,932ms               
Parsing                               1,325ms     (37,741ms)
Parsing.OperatorsExpr                35,051ms               
Parsing.OperatorsPattern              1,363ms               
Scoping                               1,949ms     (27,031ms)
Scoping.InverseScopeLookup           25,082ms               
Deserialization                       4,407ms      (6,113ms)
Deserialization.Compaction            1,706ms               
Highlighting                          1,212ms               
Import                                  324ms               
Injectivity                              73ms
```
