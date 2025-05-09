**Output of command `agda --profile=internal Final-thms.agda`:**

```
Total                            9,940,476ms              
Miscellaneous                        1,389ms              
Typing                             703,149ms (8,679,273ms)
Typing.CheckRHS                  4,445,851ms              
Typing.OccursCheck               1,586,319ms              
Typing.InstanceSearch            1,290,961ms              
Typing.TypeSig                     647,975ms              
Typing.CheckLHS                      3,998ms     (5,006ms)
Typing.CheckLHS.UnifyIndices         1,007ms              
Serialization                      345,189ms   (425,611ms)
Serialization.BuildInterface        78,459ms              
Serialization.Compress                 989ms              
Serialization.BinaryEncode             775ms              
Serialization.Sort                     196ms              
Positivity                         314,638ms              
DeadCode                               115ms   (313,620ms)
DeadCode.DeadCodeInstantiateFull   298,299ms              
DeadCode.DeadCodeReachable          15,206ms              
ProjectionLikeness                  67,001ms              
Coverage                            55,968ms    (56,657ms)
Coverage.UnifyIndices                  688ms              
Termination                            115ms    (46,323ms)
Termination.RecCheck                46,191ms              
Termination.Compare                     13ms              
Parsing                                736ms    (18,883ms)
Parsing.OperatorsExpr               17,473ms              
Parsing.OperatorsPattern               673ms              
Scoping                                994ms    (11,961ms)
Scoping.InverseScopeLookup          10,967ms              
Deserialization                      3,072ms     (4,091ms)
Deserialization.Compaction           1,019ms              
Highlighting                           710ms              
Import                                 277ms              
Injectivity                             47ms
```
