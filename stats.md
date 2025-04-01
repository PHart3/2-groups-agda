**Output of command `agda --profile=internal Biequiv-main.agda`:**

```
Total                            10,005,083ms              
Miscellaneous                           108ms              
Typing                              735,417ms (8,759,452ms)
Typing.CheckRHS                   4,429,242ms              
Typing.OccursCheck                1,659,711ms              
Typing.InstanceSearch             1,291,021ms              
Typing.TypeSig                      641,900ms              
Typing.CheckLHS                       1,265ms     (2,148ms)
Typing.CheckLHS.UnifyIndices            883ms              
Typing.With                              11ms              
Serialization                       327,238ms   (405,560ms)
Serialization.BuildInterface         76,240ms              
Serialization.Compress                  996ms              
Serialization.BinaryEncode              930ms              
Serialization.Sort                      154ms              
DeadCode                                145ms   (324,621ms)
DeadCode.DeadCodeInstantiateFull    308,913ms              
DeadCode.DeadCodeReachable           15,562ms              
Positivity                          309,180ms              
ProjectionLikeness                   65,232ms              
Termination                             115ms    (54,901ms)
Termination.RecCheck                 54,769ms              
Termination.Compare                      13ms              
Coverage                             46,174ms    (46,864ms)
Coverage.UnifyIndices                   689ms              
Parsing                                 907ms    (19,002ms)
Parsing.OperatorsExpr                17,393ms              
Parsing.OperatorsPattern                701ms              
Scoping                                 998ms    (11,734ms)
Scoping.InverseScopeLookup           10,736ms              
Deserialization                       5,584ms     (7,609ms)
Deserialization.Compaction            2,025ms              
Highlighting                            696ms              
Import                                   70ms              
Injectivity                              51ms
```
