# G913 Rule 30 compute worker

An isolated worker for the same pinned Lean sources and unchanged checker.
`prepare.py` packages public kit history, the existing Windows Lean toolchain,
compiled official imports and explicitly selected mathematical sources.
`worker.py` runs guarded checks remotely. Results and manifests are durable
evidence; `_cache/` is reproducible transfer material and safe to delete when
no worker is running. No user configuration or authentication files belong here.
