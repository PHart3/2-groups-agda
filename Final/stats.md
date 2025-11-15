**Output of command `agda --profile=internal Final-thms.agda`:**

```
Total                            10,032,791ms              
Miscellaneous                         1,957ms              
Typing                              701,084ms (8,718,433ms)
Typing.CheckRHS                   4,411,846ms              
Typing.OccursCheck                1,624,565ms              
Typing.InstanceSearch             1,334,337ms              
Typing.TypeSig                      640,636ms              
Typing.CheckLHS                       4,744ms     (5,939ms)
Typing.CheckLHS.UnifyIndices          1,194ms              
Typing.With                              23ms              
Serialization                       327,962ms   (413,600ms)
Serialization.BuildInterface         82,611ms              
Serialization.Compress                1,444ms              
Serialization.BinaryEncode            1,237ms              
Serialization.Sort                      344ms              
DeadCode                                174ms   (350,433ms)
DeadCode.DeadCodeInstantiateFull    333,418ms              
DeadCode.DeadCodeReachable           16,839ms              
Positivity                          323,439ms              
ProjectionLikeness                   70,492ms              
Termination                             128ms    (52,553ms)
Termination.RecCheck                 52,412ms              
Coverage                             48,549ms    (49,437ms)
Coverage.UnifyIndices                   888ms              
Parsing                               1,146ms    (29,581ms)
Parsing.OperatorsExpr                27,226ms              
Parsing.OperatorsPattern              1,208ms              
Scoping                               1,434ms    (15,935ms)
Scoping.InverseScopeLookup           14,500ms              
Deserialization                       4,033ms     (5,585ms)
Deserialization.Compaction            1,552ms              
Highlighting                          1,032ms              
Import                                  256ms              
Injectivity                              63ms
```
