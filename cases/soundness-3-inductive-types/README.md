# Case: soundness-3-inductive-types

## Category
Kernel Soundness - Inductive Types

## Severity
CRITICAL (if exploitable)

## Description
Tests inductive type formation rules for soundness bugs:
- Strict positivity requirements
- Non-positive occurrences
- Self-referential definitions
- Large elimination restrictions

## Attack Vectors
1. Non-strictly-positive types (function space in wrong position)
2. Reflexive types (type containing itself directly)
3. Large elimination from Prop (extracting data)
4. Mutual inductives with cycles
5. Indexed families with universe issues

## Expected Behavior
Kernel must reject:
- Non-positive occurrences
- Reflexive definitions
- Invalid large eliminations
- Universe inconsistencies in indexed families

## Obfuscation Techniques
1. **Indirection through type synonyms**: Hiding non-positivity through intermediate definitions
2. **Universe polymorphism**: Using universe variables to bypass checks
3. **Mutual induction hiding**: Spreading violation across mutually defined types
4. **Prop vs Type confusion**: Exploiting boundaries between Prop and Type
5. **Quotient types**: Using quotient constructions to hide violations

## Running
```bash
cd cases/soundness-3-inductive-types  
make test
```