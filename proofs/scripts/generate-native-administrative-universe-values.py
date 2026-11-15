from pathlib import Path

lines = [
    'import Jihoo.NativeContextualUniverseCodes',
    'set_option maxUniverseOffset 40',
    '',
    '/-! Tarski code values including administrative level32 outputs. Native',
    'universe inputs remain below32. The host level33 here only classifies codes',
    'for administrative Type32; it is never an additional native input. -/',
    'namespace Jihoo.NativeKernel.Environment.Semantics.Finite.AdministrativeValues',
    '',
    'def codeUniverse (level : Fin 33) : Universe (.type ⟨level.val+1,by omega⟩) :=',
    '  match level with',
]
for level in range(33):
    lines.append(f'  | ⟨{level},_⟩ => Finite.universe{level}')
lines += [
    '  | ⟨n+33,bound⟩ => False.elim (by omega)',
    '',
    'def decode (level : Fin 33) : Carrier (codeUniverse level) → Universe (.type ⟨level.val,by omega⟩) :=',
    '  match level with',
]
for level in range(33):
    lines.append(f'  | ⟨{level},_⟩ => fun value => .type{level} value.down')
lines += [
    '  | ⟨n+33,bound⟩ => False.elim (by omega)',
    '',
    'def encode (level : Fin 33) : Universe (.type ⟨level.val,by omega⟩) → Carrier (codeUniverse level) :=',
    '  match level with',
]
for level in range(33):
    lines.append(f'  | ⟨{level},_⟩ => fun code => ⟨Finite.decode{level} code⟩')
lines += [
    '  | ⟨n+33,bound⟩ => False.elim (by omega)',
    '',
]
for name, argument, statement, eliminated in [
    ('decode_encode', 'code : Universe (.type ⟨level.val,by omega⟩)', 'decode level (encode level code) = code', 'code'),
    ('encode_decode', 'value : Carrier (codeUniverse level)', 'encode level (decode level value) = value', 'value'),
]:
    lines += [
        f'theorem {name} (level : Fin 33) ({argument}) :',
        f'    {statement} := by',
        '  rcases level with ⟨n,bound⟩',
        '  have possibilities : ' + ' ∨ '.join(f'n = {level}' for level in range(33)) + ' := by omega',
        '  rcases possibilities with ' + ' | '.join(f'h{level}' for level in range(33)),
        f'  all_goals subst n; cases {eliminated}; rfl',
        '',
    ]
lines += [
    'theorem native_level (level : Fin 33) :',
    '    (LevelSort.type ⟨level.val,by omega⟩).native = SortTag.type level.val := rfl',
    '',
    'theorem universe_native_sort (level : Fin 33) :',
    '    (LevelSort.type ⟨level.val+1,by omega⟩).native = SortTag.type (level.val+1) := rfl',
    '',
    'theorem administrative_code_bound (level : Fin 33) : level.val < 33 := level.isLt',
    '',
    'end Jihoo.NativeKernel.Environment.Semantics.Finite.AdministrativeValues',
]
lines = lines[:-1]
lines += [
    '',
    'def empty (level : Fin 33) : Universe (.type ⟨level.val,by omega⟩) :=',
    '  match level with',
]
for level in range(33):
    lines.append(f'  | ⟨{level},_⟩ => .type{level} (ULift.{{{level}}} Empty)')
lines += [
    '  | ⟨n+33,bound⟩ => False.elim (by omega)',
    '',
    'theorem empty_uninhabited (level : Fin 33) : ¬ Nonempty (Carrier (empty level)) := by',
    '  rcases level with ⟨n,bound⟩',
    '  have possibilities : ' + ' ∨ '.join(f'n = {level}' for level in range(33)) + ' := by omega',
    '  rcases possibilities with ' + ' | '.join(f'h{level}' for level in range(33)),
    '  all_goals subst n; intro inhabited; obtain ⟨value⟩ := inhabited; exact value.down.down.elim',
    '',
    'end Jihoo.NativeKernel.Environment.Semantics.Finite.AdministrativeValues',
]

Path('Jihoo/NativeAdministrativeUniverseValues.lean').write_text('\n'.join(lines) + '\n')
