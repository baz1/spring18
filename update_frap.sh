#!/bin/bash
((echo 'NjE3YwogIHwgU3RyaW5nICJfIiVjaGFyIF8gPT4gZmFsc2UKLgo2MTRhClJlcXVpcmUgSW1wb3J0IEFzY2lpLgoKLgo=' | base64 -d) && echo w) | ed - 'frap/CompilerCorrectness_template.v'
((echo 'OTA1YwogIHwgU3RyaW5nICJfIiVjaGFyIF8gPT4gZmFsc2UKLgo5MDJhClJlcXVpcmUgSW1wb3J0IEFzY2lpLgoKLgo=' | base64 -d) && echo w) | ed - 'frap/CompilerCorrectness.v'
((echo 'NzM0YwpBcmd1bWVudHMgRmFpbGVkIHtyZXN1bHR9LgooKiBJbXBsaWNpdCBBcmd1bWVudHMgRmFpbGVkIFtyZXN1bHRdLiAqKQouCg==' | base64 -d) && echo w) | ed - 'frap/DeepAndShallowEmbeddings_template.v'
((echo 'ODg5YwogIEFyZ3VtZW50cyBGYWlsZWQge3Jlc3VsdH0uCi4K' | base64 -d) && echo w) | ed - 'frap/DeepAndShallowEmbeddings.v'
((echo 'MTE2MmMKQXJndW1lbnRzIHNwbGl0IHtQMX0ge1AyfS4KKCogSW1wbGljaXQgQXJndW1lbnRzIHNwbGl0IFtQMSBQMl0uICopCi4K' | base64 -d) && echo w) | ed - 'frap/DependentInductiveTypes.v'
((echo 'Mjc3LDI3OGQKMjc0YQpSZXF1aXJlIEltcG9ydCBMaXN0U2V0LgoKLgo=' | base64 -d) && echo w) | ed - 'frap/ProofByReflection_template.v'
((echo 'NTk1LDU5NmQKNTg4YQpSZXF1aXJlIEltcG9ydCBMaXN0U2V0LgoKLgo=' | base64 -d) && echo w) | ed - 'frap/ProofByReflection.v'
((echo 'Nzc2YQpTZXQgTmVzdGVkIFByb29mcyBBbGxvd2VkLgoKLgo=' | base64 -d) && echo w) | ed - 'frap/SharedMemory.v'
