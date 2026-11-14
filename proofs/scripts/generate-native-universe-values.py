from pathlib import Path

lines = [
    'import Jihoo.NativeContextualUniverseCodes',
    'set_option maxUniverseOffset 40',
    '',
    '/-! Generic finite-level Tarski code values for every native input universe.',
    'The level-indexed operations reduce to the concrete previously verified',
    'host universes; no semantic membership or normalization is an input. -/',
    'namespace Jihoo.NativeKernel.Environment.Semantics.Finite.Values',
    '',
    'def codeUniverse (level : Fin 32) : Universe (.type ⟨level.val+1,by omega⟩) :=',
    '  match level with',
]
for level in range(32):
    lines.append(f'  | ⟨{level},_⟩ => Finite.universe{level}')
lines += [
    '  | ⟨n+32,bound⟩ => False.elim (by omega)',
    '',
    'def decode (level : Fin 32) : Carrier (codeUniverse level) → Universe (.type ⟨level.val,by omega⟩) :=',
    '  match level with',
]
for level in range(32):
    lines.append(f'  | ⟨{level},_⟩ => fun value => .type{level} value.down')
lines += [
    '  | ⟨n+32,bound⟩ => False.elim (by omega)',
    '',
    'def encode (level : Fin 32) : Universe (.type ⟨level.val,by omega⟩) → Carrier (codeUniverse level) :=',
    '  match level with',
]
for level in range(32):
    lines.append(f'  | ⟨{level},_⟩ => fun code => ⟨Finite.decode{level} code⟩')
lines += [
    '  | ⟨n+32,bound⟩ => False.elim (by omega)',
    '',
]
for name, argument, statement, eliminated in [
    ('decode_encode', 'code : Universe (.type ⟨level.val,by omega⟩)', 'decode level (encode level code) = code', 'code'),
    ('encode_decode', 'value : Carrier (codeUniverse level)', 'encode level (decode level value) = value', 'value'),
]:
    lines += [
        f'theorem {name} (level : Fin 32) ({argument}) :',
        f'    {statement} := by',
        '  rcases level with ⟨n,bound⟩',
        '  have possibilities : ' + ' ∨ '.join(f'n = {level}' for level in range(32)) + ' := by omega',
        '  rcases possibilities with ' + ' | '.join(f'h{level}' for level in range(32)),
        f'  all_goals subst n; cases {eliminated}; rfl',
        '',
    ]
lines += [
    'theorem native_level (level : Fin 32) :',
    '    (LevelSort.type ⟨level.val,by omega⟩).native = SortTag.type level.val := rfl',
    '',
    'theorem universe_native_sort (level : Fin 32) :',
    '    (LevelSort.type ⟨level.val+1,by omega⟩).native = SortTag.type (level.val+1) := rfl',
    '',
    'theorem universe_input_bound (level : Fin 32) : level.val < 32 := level.isLt',
    '',
    'end Jihoo.NativeKernel.Environment.Semantics.Finite.Values',
]
lines = lines[:-1]
lines += [
    '',
    'def empty (level : Fin 32) : Universe (.type ⟨level.val,by omega⟩) :=',
    '  match level with',
]
for level in range(32):
    lines.append(f'  | ⟨{level},_⟩ => .type{level} (ULift.{{{level}}} Empty)')
lines += [
    '  | ⟨n+32,bound⟩ => False.elim (by omega)',
    '',
    'theorem empty_uninhabited (level : Fin 32) : ¬ Nonempty (Carrier (empty level)) := by',
    '  rcases level with ⟨n,bound⟩',
    '  have possibilities : ' + ' ∨ '.join(f'n = {level}' for level in range(32)) + ' := by omega',
    '  rcases possibilities with ' + ' | '.join(f'h{level}' for level in range(32)),
    '  all_goals subst n; intro inhabited; obtain ⟨value⟩ := inhabited; exact value.down.down.elim',
    '',
    'end Jihoo.NativeKernel.Environment.Semantics.Finite.Values',
]

Path('Jihoo/NativeFiniteUniverseValues.lean').write_text('\n'.join(lines) + '\n')
