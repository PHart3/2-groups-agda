**Output of command `agda --profile=internal Biequiv-main.agda`:**

```
Total                            10,000,460ms              
Miscellaneous                           226ms              
Typing                              710,206ms (8,770,022ms)
Typing.CheckRHS                   4,438,188ms              
Typing.OccursCheck                1,671,014ms              
Typing.InstanceSearch             1,303,872ms              
Typing.TypeSig                      644,587ms              
Typing.CheckLHS                       1,268ms     (2,142ms)
Typing.CheckLHS.UnifyIndices            874ms              
Typing.With                              10ms              
Serialization                       330,495ms   (408,886ms)
Serialization.BuildInterface         76,189ms              
Serialization.BinaryEncode            1,038ms              
Serialization.Compress                1,003ms              
Serialization.Sort                      159ms              
DeadCode                                138ms   (310,645ms)
DeadCode.DeadCodeInstantiateFull    290,645ms              
DeadCode.DeadCodeReachable           19,861ms              
Positivity                          288,326ms              
ProjectionLikeness                   81,278ms              
Termination                             115ms    (60,864ms)
Termination.RecCheck                 60,732ms              
Termination.Compare                      13ms              
Coverage                             40,494ms    (41,178ms)
Coverage.UnifyIndices                   684ms              
Parsing                                 858ms    (18,938ms)
Parsing.OperatorsExpr                17,375ms              
Parsing.OperatorsPattern                704ms              
Scoping                                 986ms    (11,715ms)
Scoping.InverseScopeLookup           10,729ms              
Deserialization                       5,516ms     (7,490ms)
Deserialization.Compaction            1,973ms              
Highlighting                            753ms              
Import                                   85ms              
Injectivity                              48ms
```
