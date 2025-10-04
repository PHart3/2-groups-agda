**Output of command `agda --profile=internal Final-thms.agda`:**

```
Total                            10,037,652ms              
Miscellaneous                         1,796ms              
Typing                              709,091ms (8,704,258ms)
Typing.CheckRHS                   4,388,828ms              
Typing.OccursCheck                1,631,524ms              
Typing.InstanceSearch             1,331,265ms              
Typing.TypeSig                      635,307ms              
Typing.CheckLHS                       6,938ms     (8,218ms)
Typing.CheckLHS.UnifyIndices          1,279ms              
Typing.With                              23ms              
Serialization                       377,790ms   (463,522ms)
Serialization.BuildInterface         82,978ms              
Serialization.Compress                1,397ms              
Serialization.BinaryEncode            1,117ms              
Serialization.Sort                      238ms              
Positivity                          325,734ms              
DeadCode                                179ms   (320,922ms)
DeadCode.DeadCodeInstantiateFull    304,882ms              
DeadCode.DeadCodeReachable           15,861ms              
ProjectionLikeness                   63,541ms              
Termination                             167ms    (59,671ms)
Termination.RecCheck                 59,484ms              
Termination.Compare                      14ms              
Coverage                             47,814ms    (48,702ms)
Coverage.UnifyIndices                   887ms              
Parsing                                 976ms    (27,594ms)
Parsing.OperatorsExpr                25,492ms              
Parsing.OperatorsPattern              1,125ms              
Scoping                               1,335ms    (15,530ms)
Scoping.InverseScopeLookup           14,195ms              
Deserialization                       3,713ms     (5,132ms)
Deserialization.Compaction            1,418ms              
Highlighting                            941ms              
Import                                  247ms              
Injectivity                              60ms              
```
