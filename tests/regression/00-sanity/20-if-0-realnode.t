  $ cfgDot 20-if-0-realnode.c

  $ graph-easy --as=boxart main.dot
  ┌─────────────────────────────────────────┐
  │ main()                                  │
  └─────────────────────────────────────────┘
    │
    │ (body)
    ▼
  ┌─────────────────────────────────────────┐
  │ 20-if-0-realnode.c:8:5-14:5             │
  │ (20-if-0-realnode.c:8:9-8:10)           │
  │ [20-if-0-realnode.c:7:5-8:5             │   Neg(0)
  │ (unknown)]                              │ ─────────┐
  │ YAML loc: 20-if-0-realnode.c:8:5-14:5   │          │
  │ GraphML: true; server: true             │ ◀────────┘
  └─────────────────────────────────────────┘
    │
    │ Pos(0)
    ▼
  ┌─────────────────────────────────────────┐
  │ 20-if-0-realnode.c:10:9-10:16           │
  │ (20-if-0-realnode.c:10:9-10:16)         │
  │ YAML loc: 20-if-0-realnode.c:10:9-10:16 │
  │ GraphML: true; server: true             │
  └─────────────────────────────────────────┘
    │
    │ stuff()
    ▼
  ┌─────────────────────────────────────────┐
  │ 20-if-0-realnode.c:15:5-15:13           │
  │ (20-if-0-realnode.c:15:12-15:13)        │
  │ YAML loc: 20-if-0-realnode.c:15:5-15:13 │
  │ GraphML: true; server: true             │
  └─────────────────────────────────────────┘
    │
    │ return 0
    ▼
  ┌─────────────────────────────────────────┐
  │ return of main()                        │
  └─────────────────────────────────────────┘
