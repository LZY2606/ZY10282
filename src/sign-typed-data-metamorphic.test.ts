/*
 * Digest metamorphic tests for EIP-712 typed data (V3/V4) plus fixed-key
 * sign/recover roundtrips.
 *
 * Unlike the fixed reference vectors in `sign-typed-data.test.ts`, these tests
 * do not rely on precomputed random signatures. They assert properties of the
 * encoding pipeline itself:
 *
 * - Invariant transforms (types object key reordering, message property
 *   reordering, adding unrelated types, explicit equivalent value encodings)
 *   must preserve both the digest and the encoded bytes.
 * - Mutation transforms (field declaration order, primary type, array element
 *   order, domain chainId, a single value bit) are only asserted to change the
 *   digest where the encoded preimage is constructed by this test and is known
 *   to differ on a small fixture; the encoded bytes are compared too, so the
 *   assertion never rests on a hash property alone. Hash collisions are never
 *   claimed to be impossible.
 * - A fixed-seed generator builds bounded type graphs (including arrays,
 *   recursive structs and null leaves) and runs the same relations across them.
 *   On failure the case is shrunk (seed plus reduced bounds) and reported with
 *   the schema, message and failing relation path.
 * - Three encoder-bug mutants (declaration-order dependency sorting, missing
 *   one array hash layer, wrong signed integer extension) get dedicated
 *   negative-control fixtures proving the suite detects them.
 *
 * Sign/recover is only exercised on one fixed private key for roundtripping.
 */

/*
 * Assertions are shared through the expectSameEncoding,
 * expectDifferentMessageEncoding and check helpers below.
 */
/* eslint-disable jest/expect-expect */

import * as ethUtil from '@ethereumjs/util';
import { encode } from '@metamask/abi-utils';
import { bytesToHex, concatBytes } from '@metamask/utils';
import { keccak256 } from 'ethereum-cryptography/keccak';

import {
  recoverTypedSignature,
  signTypedData,
  SignTypedDataVersion,
  TypedDataUtils,
} from './sign-typed-data';
import type {
  MessageTypeProperty,
  MessageTypes,
  TypedDataV1,
  TypedMessage,
} from './sign-typed-data';

type Version = SignTypedDataVersion.V3 | SignTypedDataVersion.V4;

const PRIVATE_KEY = Buffer.from(
  '4af1bceebf7f3634ec3cff8a2c38e51178d5d4ce585c52d6043e5e2cc3418bb0',
  'hex',
);
const SIGNER_ADDRESS = ethUtil.addHexPrefix(
  ethUtil.privateToAddress(PRIVATE_KEY).toString('hex'),
);

const INT256_MIN = -(BigInt(2) ** BigInt(255));
const INT256_SIGNED_MAX = BigInt(2) ** BigInt(255) - BigInt(1);
const UINT256_MAX = BigInt(2) ** BigInt(256) - BigInt(1);

const EIP_VERSION_V3 = SignTypedDataVersion.V3;
const EIP_VERSION_V4 = SignTypedDataVersion.V4;

const DOMAIN_TYPE_FIELDS: MessageTypeProperty[] = [
  { name: 'name', type: 'string' },
  { name: 'version', type: 'string' },
  { name: 'chainId', type: 'uint256' },
  { name: 'verifyingContract', type: 'address' },
];

const DOMAIN = {
  name: 'Ether Mail',
  version: '1',
  chainId: 1,
  verifyingContract: '0xCcCCccccCCCCcCCCCCCcCcCccCcCCCcCcccccccC',
};

/**
 * Structured deep clone (structuredClone is not in the ES2020 type libs).
 * Immutable primitives (including bigint) are returned as-is.
 *
 * @param value - The value to clone.
 * @returns A structurally independent copy of the input.
 */
function deepClone<T>(value: T): T {
  if (Array.isArray(value)) {
    return value.map(deepClone) as T;
  }
  if (
    value !== null &&
    typeof value === 'object' &&
    !(value instanceof Uint8Array)
  ) {
    return Object.fromEntries(
      Object.entries(value).map(([key, child]) => [key, deepClone(child)]),
    ) as T;
  }
  return value;
}

/**
 * Compute the final EIP-712 digest of a typed message as a hex string.
 *
 * @param data - The typed message.
 * @param version - The EIP-712 version to encode with.
 * @returns The `0x`-prefixed 32-byte digest.
 */
function digestOf(data: TypedMessage<MessageTypes>, version: Version): string {
  return bytesToHex(TypedDataUtils.eip712Hash(data, version));
}

/**
 * Encode the primary message struct (the preimage of its struct hash).
 *
 * @param data - The typed message.
 * @param version - The EIP-712 version to encode with.
 * @returns The `0x`-prefixed ABI-like encoded bytes.
 */
function encodedMessageOf(
  data: TypedMessage<MessageTypes>,
  version: Version,
): string {
  return bytesToHex(
    TypedDataUtils.encodeData(
      data.primaryType as string,
      data.message,
      data.types,
      version,
    ),
  );
}

/**
 * Compute the EIP-712 domain separator hash as a hex string.
 *
 * @param data - The typed message whose domain is hashed.
 * @param version - The EIP-712 version to encode with.
 * @returns The `0x`-prefixed 32-byte domain hash.
 */
function domainHashOf(
  data: TypedMessage<MessageTypes>,
  version: Version,
): string {
  return bytesToHex(TypedDataUtils.eip712DomainHash(data, version));
}

/**
 * Swap the case of every hexadecimal letter in an `0x`-prefixed hex string.
 *
 * @param hex - The input hex string.
 * @returns A semantically identical hex string with swapped letter case.
 */
function swapHexCase(hex: string): string {
  return hex.replace(/[a-fA-F]/gu, (character) =>
    character === character.toLowerCase()
      ? character.toUpperCase()
      : character.toLowerCase(),
  );
}

/**
 * Reverse the insertion order of every object's own keys, recursively.
 * Arrays keep their element order.
 *
 * @param value - The value whose object keys should be reversed.
 * @returns A copy with every object's own keys inserted in reverse order.
 */
function reverseKeysDeep(value: unknown): unknown {
  if (Array.isArray(value)) {
    return value.map(reverseKeysDeep);
  }
  if (
    value !== null &&
    typeof value === 'object' &&
    !(value instanceof Uint8Array)
  ) {
    return Object.fromEntries(
      Object.entries(value)
        .reverse()
        .map(([key, child]) => [key, reverseKeysDeep(child)]),
    );
  }
  return value;
}

/**
 * Rebuild the `types` object with its keys in reverse insertion order.
 *
 * @param data - The typed message to transform.
 * @returns A copy whose `types` object has reversed key order.
 */
function reorderTypesObjectKeys<T extends MessageTypes>(
  data: TypedMessage<T>,
): TypedMessage<T> {
  return {
    ...data,
    types: Object.fromEntries(Object.entries(data.types).reverse()) as T,
  };
}

/**
 * Rebuild the message object (recursively) with reversed property order.
 *
 * @param data - The typed message to transform.
 * @returns A copy whose message properties are reversed at every level.
 */
function reorderMessageKeys<T extends MessageTypes>(
  data: TypedMessage<T>,
): TypedMessage<T> {
  return {
    ...data,
    message: reverseKeysDeep(data.message) as TypedMessage<T>['message'],
  };
}

/**
 * Add types that the primary type's dependency graph never references.
 *
 * @param data - The typed message to transform.
 * @returns A copy with additional unused type declarations.
 */
function withUnrelatedTypes<T extends MessageTypes>(
  data: TypedMessage<T>,
): TypedMessage<T> {
  const types = {
    ...deepClone(data.types),
    UnusedAaa: [{ name: 'first', type: 'uint256' }],
    UnusedZzz: [
      { name: 'a', type: 'UnusedAaa' },
      { name: 'b', type: 'address[2]' },
    ],
  };
  return { ...data, types: types as T };
}

/**
 * Swap two field declarations within one struct type.
 *
 * @param data - The typed message to transform.
 * @param typeName - The struct whose field order changes.
 * @param indexA - Index of the first field to swap.
 * @param indexB - Index of the second field to swap.
 * @returns A copy with the two field declarations exchanged.
 */
function swapDeclaredFields<T extends MessageTypes>(
  data: TypedMessage<T>,
  typeName: string,
  indexA: number,
  indexB: number,
): TypedMessage<T> {
  const fields = [...data.types[typeName]];
  const [first, second] = [fields[indexA], fields[indexB]];
  fields[indexA] = second;
  fields[indexB] = first;
  return { ...data, types: { ...data.types, [typeName]: fields } };
}

/**
 * Rename a struct type everywhere it appears (key, primaryType, field types).
 *
 * @param data - The typed message to transform.
 * @param oldName - The existing struct type name.
 * @param newName - The replacement struct type name.
 * @returns A copy using the new name in the types object, field types and
 * primary type.
 */
function renameType<T extends MessageTypes>(
  data: TypedMessage<T>,
  oldName: string,
  newName: string,
): TypedMessage<T> {
  const baseTypePattern = new RegExp(`^${oldName}(?=\\[|$)`, 'u');
  const types = Object.fromEntries(
    Object.entries(data.types).map(([name, fields]) => [
      name === oldName ? newName : name,
      fields.map((field) => ({
        ...field,
        type: field.type.replace(baseTypePattern, newName),
      })),
    ]),
  ) as T;
  return {
    ...data,
    types,
    primaryType: (data.primaryType === oldName
      ? newName
      : data.primaryType) as keyof T,
  };
}

type Path = (string | number)[];

/**
 * Read a value at a sequence of object/array keys.
 *
 * @param currentRoot - The value to read from.
 * @param path - The sequence of keys to follow.
 * @returns The value found at the path.
 */
function getAtPath(currentRoot: unknown, path: Path): unknown {
  return path.reduce<unknown>((current, key) => {
    return (current as Record<string | number, unknown>)[key];
  }, currentRoot);
}

/**
 * Assign a value at a sequence of object/array keys.
 *
 * @param currentRoot - The value to mutate.
 * @param path - The sequence of keys to follow.
 * @param value - The value to assign.
 */
function setAtPath(currentRoot: unknown, path: Path, value: unknown): void {
  const parent = getAtPath(currentRoot, path.slice(0, -1)) as Record<
    string | number,
    unknown
  >;
  parent[path[path.length - 1]] = value;
}

/* eslint-disable @typescript-eslint/no-explicit-any */

// --- Rich V4 fixture: structs, struct arrays, dynamic/fixed nested arrays,
// integer extremes, bytesN, bool, nullable struct field. ---

const MAIL_TYPES = {
  EIP712Domain: DOMAIN_TYPE_FIELDS,
  Person: [
    { name: 'name', type: 'string' },
    { name: 'wallet', type: 'address' },
  ],
  Mail: [
    { name: 'from', type: 'Person' },
    { name: 'to', type: 'Person' },
    { name: 'cc', type: 'Person[]' },
    { name: 'contents', type: 'string' },
    { name: 'small', type: 'int8' },
    { name: 'big', type: 'int256' },
    { name: 'huge', type: 'uint256' },
    { name: 'payload', type: 'bytes4' },
    { name: 'tags', type: 'string[]' },
    { name: 'matrix', type: 'uint8[2][2]' },
    { name: 'flag', type: 'bool' },
    { name: 'optional', type: 'Person' },
  ],
};

const MAIL_MESSAGE = {
  from: {
    name: 'Cow',
    wallet: '0xCD2a3d9F938E13CD947Ec05AbC7FE734Df8DD826',
  },
  to: {
    name: 'Bob',
    wallet: '0xbBbBBBBbbBBBbbbBbbBbbbbBBbBbbbbBbBbbBBbB',
  },
  cc: [
    {
      name: 'Ann',
      wallet: '0xaAaAaAaaAaAaAaaAaAAAAAAAAaaaAaAaAaaAaaAa',
    },
    {
      name: 'Dan',
      wallet: '0xdDddDDdDDDDdDdDDdDDdDDdDDdDDdDDdDDdDDd',
    },
  ],
  contents: 'Hello, Bob!',
  small: -128,
  big: INT256_MIN,
  huge: UINT256_MAX,
  payload: '0x12345678',
  tags: ['work', 'urgent'],
  matrix: [
    [1, 2],
    [3, 4],
  ],
  flag: true,
  optional: null,
};

/**
 * Build a fresh independent copy of the rich V4 fixture.
 *
 * @returns A typed message using the rich Mail schema.
 */
function mailData(): TypedMessage<MessageTypes> {
  return {
    types: deepClone(MAIL_TYPES),
    primaryType: 'Mail',
    domain: { ...DOMAIN },
    message: deepClone(MAIL_MESSAGE),
  };
}

// --- Flat V3-compatible fixture: no arrays, no recursion. ---

const FLAT_TYPES = {
  EIP712Domain: DOMAIN_TYPE_FIELDS,
  Person: [
    { name: 'name', type: 'string' },
    { name: 'wallet', type: 'address' },
  ],
  Mail: [
    { name: 'from', type: 'Person' },
    { name: 'subject', type: 'string' },
    { name: 'urgent', type: 'bool' },
    { name: 'score', type: 'int8' },
  ],
};

const FLAT_MESSAGE = {
  from: {
    name: 'Cow',
    wallet: '0xCD2a3d9F938E13CD947Ec05AbC7FE734Df8DD826',
  },
  subject: 'Hello',
  urgent: true,
  score: -1,
};

/**
 * Build a fresh independent copy of the flat V3-compatible fixture.
 *
 * @returns A typed message using the flat Mail schema.
 */
function flatData(): TypedMessage<MessageTypes> {
  return {
    types: deepClone(FLAT_TYPES),
    primaryType: 'Mail',
    domain: { ...DOMAIN },
    message: deepClone(FLAT_MESSAGE),
  };
}

/**
 * Assert that two messages share both the digest and the message encoding
 * bytes. The encoded bytes comparison is strictly stronger than comparing
 * digests alone.
 *
 * @param base - The reference message.
 * @param variant - The message expected to be an equivalent encoding.
 * @param version - The EIP-712 version to encode with.
 */
function expectSameEncoding(
  base: TypedMessage<MessageTypes>,
  variant: TypedMessage<MessageTypes>,
  version: Version,
): void {
  expect(encodedMessageOf(variant, version)).toBe(
    encodedMessageOf(base, version),
  );
  expect(digestOf(variant, version)).toBe(digestOf(base, version));
}

/**
 * Assert a mutation changes both the digest and the message encoding bytes.
 * The caller constructs both messages so the preimage difference is known;
 * these are small, fixed fixtures and no hash-collision claim is made.
 *
 * @param base - The reference message.
 * @param variant - The mutated message with a known different preimage.
 * @param version - The EIP-712 version to encode with.
 */
function expectDifferentMessageEncoding(
  base: TypedMessage<MessageTypes>,
  variant: TypedMessage<MessageTypes>,
  version: Version,
): void {
  expect(encodedMessageOf(variant, version)).not.toBe(
    encodedMessageOf(base, version),
  );
  expect(digestOf(variant, version)).not.toBe(digestOf(base, version));
}

describe('digest invariants: transforms that must preserve the digest', () => {
  it('v4: reordering the keys of the types object preserves digest and bytes', () => {
    const base = mailData();
    expectSameEncoding(
      base,
      reorderTypesObjectKeys(deepClone(base)),
      EIP_VERSION_V4,
    );
  });

  it('v3: reordering the keys of the types object preserves digest and bytes', () => {
    const base = flatData();
    expectSameEncoding(
      base,
      reorderTypesObjectKeys(deepClone(base)),
      EIP_VERSION_V3,
    );
  });

  it('v4: deeply reordering message properties preserves digest and bytes', () => {
    const base = mailData();
    expectSameEncoding(
      base,
      reorderMessageKeys(deepClone(base)),
      EIP_VERSION_V4,
    );
  });

  it('v3: reordering message properties preserves digest and bytes', () => {
    const base = flatData();
    expectSameEncoding(
      base,
      reorderMessageKeys(deepClone(base)),
      EIP_VERSION_V3,
    );
  });

  it('v4: adding types unrelated to the dependency graph preserves digest and bytes', () => {
    const base = mailData();
    expectSameEncoding(
      base,
      withUnrelatedTypes(deepClone(base)),
      EIP_VERSION_V4,
    );
  });

  it('v3: adding types unrelated to the dependency graph preserves digest and bytes', () => {
    const base = flatData();
    expectSameEncoding(
      base,
      withUnrelatedTypes(deepClone(base)),
      EIP_VERSION_V3,
    );
  });

  // Every mutator below produces an explicitly equivalent encoding of the
  // same preimage, using a different input representation.
  const equivalentVariants: [string, (data: any) => void][] = [
    [
      'int8 extreme as decimal string',
      (data) => {
        data.message.small = '-128';
      },
    ],
    [
      'int8 extreme as bigint',
      (data) => {
        data.message.small = BigInt(-128);
      },
    ],
    [
      'int256 minimum as decimal string',
      (data) => {
        data.message.big = INT256_MIN.toString(10);
      },
    ],
    [
      'int256 minimum as bigint',
      (data) => {
        data.message.big = INT256_MIN;
      },
    ],
    [
      'uint256 maximum as hex string',
      (data) => {
        data.message.huge = `0x${'ff'.repeat(32)}`;
      },
    ],
    [
      'uint256 maximum as decimal string',
      (data) => {
        data.message.huge = UINT256_MAX.toString(10);
      },
    ],
    [
      'bytes4 from hex and from a number are equivalent',
      (data) => {
        data.message.payload = 0x12345678;
      },
    ],
    [
      'bytes4 from hex and from a byte array are equivalent',
      (data) => {
        data.message.payload = new Uint8Array([0x12, 0x34, 0x56, 0x78]);
      },
    ],
    [
      'bool true and the string "true" are equivalent',
      (data) => {
        data.message.flag = 'true';
      },
    ],
    [
      'checksummed and lowercase addresses are equivalent',
      (data) => {
        data.message.from.wallet = data.message.from.wallet.toLowerCase();
      },
    ],
    [
      'checksummed and uppercase-hex addresses are equivalent',
      (data) => {
        data.message.to.wallet = `0x${(data.message.to.wallet as string)
          .slice(2)
          .toUpperCase()}`;
      },
    ],
    [
      'verifyingContract case variants are equivalent',
      (data) => {
        data.domain.verifyingContract = swapHexCase(
          data.domain.verifyingContract,
        );
      },
    ],
    [
      'chainId as a number, decimal string and hex string are equivalent',
      (data) => {
        data.domain.chainId = '0x1';
      },
    ],
    [
      'nested fixed-array elements as strings are equivalent',
      (data) => {
        data.message.matrix = [
          ['1', '2'],
          ['3', '4'],
        ];
      },
    ],
    [
      'string array, struct array and all nested objects reordered',
      (data) => {
        const reordered = reorderMessageKeys(deepClone(data));
        data.message = reordered.message;
        data.types = reorderTypesObjectKeys(reordered).types;
      },
    ],
  ];

  equivalentVariants.forEach(([description, mutate]) => {
    it(`V4: ${description}`, () => {
      const base = mailData();
      const variant = mailData();
      mutate(variant);
      expectSameEncoding(base, variant, EIP_VERSION_V4);
    });
  });

  const flatEquivalentVariants: [string, (data: any) => void][] = [
    [
      'bool as the string "true"',
      (data) => {
        data.message.urgent = 'true';
      },
    ],
    [
      'int8 value as decimal string',
      (data) => {
        data.message.score = '-1';
      },
    ],
    [
      'int8 value as bigint',
      (data) => {
        data.message.score = BigInt(-1);
      },
    ],
    [
      'address case swap',
      (data) => {
        data.message.from.wallet = swapHexCase(data.message.from.wallet);
      },
    ],
    [
      'chainId as a string',
      (data) => {
        data.domain.chainId = '1';
      },
    ],
  ];

  flatEquivalentVariants.forEach(([description, mutate]) => {
    it(`V3: ${description}`, () => {
      const base = flatData();
      const variant = flatData();
      mutate(variant);
      expectSameEncoding(base, variant, EIP_VERSION_V3);
    });
  });
});

describe('digest mutations: changes that must alter digest and encoded bytes', () => {
  it('v4: swapping the declaration order of two fields changes digest and bytes', () => {
    const base = mailData();
    const variant = swapDeclaredFields(deepClone(base), 'Mail', 0, 1);
    expect(TypedDataUtils.encodeType('Mail', variant.types)).not.toBe(
      TypedDataUtils.encodeType('Mail', base.types),
    );
    expectDifferentMessageEncoding(base, variant, EIP_VERSION_V4);
  });

  it('v3: swapping the declaration order of two fields changes digest and bytes', () => {
    const base = flatData();
    const variant = swapDeclaredFields(deepClone(base), 'Mail', 0, 1);
    expectDifferentMessageEncoding(base, variant, EIP_VERSION_V3);
  });

  it('v4: renaming the primary type changes the type string, digest and bytes', () => {
    const base = mailData();
    const variant = renameType(deepClone(base), 'Mail', 'RenamedMail');
    expect(variant.primaryType).toBe('RenamedMail');
    expect(TypedDataUtils.encodeType('RenamedMail', variant.types)).toContain(
      'RenamedMail(',
    );
    expectDifferentMessageEncoding(base, variant, EIP_VERSION_V4);
  });

  it('v3: renaming the primary type changes the type string, digest and bytes', () => {
    const base = flatData();
    const variant = renameType(deepClone(base), 'Mail', 'RenamedMail');
    expectDifferentMessageEncoding(base, variant, EIP_VERSION_V3);
  });

  it('v4: swapping dynamic array elements changes digest and bytes', () => {
    const base = mailData();
    const variant: any = deepClone(base);
    [variant.message.tags[0], variant.message.tags[1]] = [
      variant.message.tags[1],
      variant.message.tags[0],
    ];
    expectDifferentMessageEncoding(base, variant, EIP_VERSION_V4);
  });

  it('v4: swapping rows of a fixed nested array changes digest and bytes', () => {
    const base = mailData();
    const variant: any = deepClone(base);
    [variant.message.matrix[0], variant.message.matrix[1]] = [
      variant.message.matrix[1],
      variant.message.matrix[0],
    ];
    expectDifferentMessageEncoding(base, variant, EIP_VERSION_V4);
  });

  it('v4: swapping elements of a struct array changes digest and bytes', () => {
    const base = mailData();
    const variant: any = deepClone(base);
    [variant.message.cc[0], variant.message.cc[1]] = [
      variant.message.cc[1],
      variant.message.cc[0],
    ];
    expectDifferentMessageEncoding(base, variant, EIP_VERSION_V4);
  });

  it('v4: changing domain chainId changes the domain hash and the digest', () => {
    const base = mailData();
    const variant = deepClone(base);
    (variant.domain as any).chainId = 2;
    expect(domainHashOf(variant, EIP_VERSION_V4)).not.toBe(
      domainHashOf(base, EIP_VERSION_V4),
    );
    expect(digestOf(variant, EIP_VERSION_V4)).not.toBe(
      digestOf(base, EIP_VERSION_V4),
    );
    // The message encoding itself does not include the domain.
    expect(encodedMessageOf(variant, EIP_VERSION_V4)).toBe(
      encodedMessageOf(base, EIP_VERSION_V4),
    );
  });

  it('v3: changing domain chainId changes the domain hash and the digest', () => {
    const base = flatData();
    const variant = deepClone(base);
    (variant.domain as any).chainId = 2;
    expect(domainHashOf(variant, EIP_VERSION_V3)).not.toBe(
      domainHashOf(base, EIP_VERSION_V3),
    );
    expect(digestOf(variant, EIP_VERSION_V3)).not.toBe(
      digestOf(base, EIP_VERSION_V3),
    );
  });

  it('v4: flipping the low bit of int256 minimum changes digest and bytes', () => {
    const base = mailData();
    const variant = deepClone(base);
    // eslint-disable-next-line no-bitwise -- flipping the low bit is the mutation under test
    variant.message.big = (INT256_MIN ^ BigInt(1)) as any;
    expect(variant.message.big).toBe(INT256_MIN + BigInt(1));
    expectDifferentMessageEncoding(base, variant, EIP_VERSION_V4);
  });

  it('v4: flipping one nibble of a bytes4 value changes digest and bytes', () => {
    const base = mailData();
    const variant = deepClone(base);
    variant.message.payload = '0x12345679';
    expectDifferentMessageEncoding(base, variant, EIP_VERSION_V4);
  });

  it('v4: flipping a bool value changes digest and bytes', () => {
    const base = mailData();
    const variant = deepClone(base);
    variant.message.flag = false;
    expectDifferentMessageEncoding(base, variant, EIP_VERSION_V4);
  });

  it('v3: flipping the low bit of an int8 value changes digest and bytes', () => {
    const base = flatData();
    const variant = deepClone(base);
    variant.message.score = -2;
    // eslint-disable-next-line no-bitwise -- documents that -2 is -1 with the low bit flipped
    expect(BigInt(-1) ^ BigInt(1)).toBe(BigInt(-2));
    expectDifferentMessageEncoding(base, variant, EIP_VERSION_V3);
  });
});

describe('boundary coverage: integer extremes and bytesN widths', () => {
  type IntegerCase = {
    type: string;
    minimum: bigint;
    maximum: bigint;
    versions: Version[];
  };

  const integerCases: IntegerCase[] = [
    {
      type: 'int8',
      minimum: BigInt(-128),
      maximum: BigInt(127),
      versions: [EIP_VERSION_V3, EIP_VERSION_V4],
    },
    {
      type: 'int256',
      minimum: INT256_MIN,
      maximum: INT256_SIGNED_MAX,
      versions: [EIP_VERSION_V3, EIP_VERSION_V4],
    },
    {
      type: 'uint256',
      minimum: BigInt(0),
      maximum: UINT256_MAX,
      versions: [EIP_VERSION_V3, EIP_VERSION_V4],
    },
  ];

  /**
   * Build a single-field integer message for extremum equivalence checks.
   *
   * @param type - The Solidity integer type of the sole field.
   * @param value - The field value in one of its accepted representations.
   * @returns A typed message with the single `Data.value` field.
   */
  function singleIntegerData(
    type: string,
    value: unknown,
  ): TypedMessage<MessageTypes> {
    return {
      types: {
        EIP712Domain: DOMAIN_TYPE_FIELDS,
        Data: [{ name: 'value', type }],
      },
      primaryType: 'Data',
      domain: { ...DOMAIN },
      message: { value },
    };
  }

  integerCases.forEach(({ type, minimum, maximum, versions }) => {
    versions.forEach((version) => {
      it(`${version}: ${type} minimum accepts decimal string and bigint identically`, () => {
        expectSameEncoding(
          singleIntegerData(type, minimum.toString(10)),
          singleIntegerData(type, minimum),
          version,
        );
      });

      it(`${version}: ${type} maximum accepts decimal string, bigint and hex string identically`, () => {
        expectSameEncoding(
          singleIntegerData(type, maximum.toString(10)),
          singleIntegerData(type, maximum),
          version,
        );
        expectSameEncoding(
          singleIntegerData(type, maximum),
          singleIntegerData(type, `0x${maximum.toString(16)}`),
          version,
        );
      });
    });
  });

  for (let length = 1; length <= 32; length += 1) {
    it(`V4: bytes${length} accepts hex and byte-array identically but rejects a shorter width`, () => {
      const full = new Uint8Array(
        Array.from({ length }, (_, index) => (index % 2 === 0 ? 0xab : 0xcd)),
      );
      const fullHex = bytesToHex(full);
      const shorterHex = bytesToHex(full.subarray(0, length - 1));
      const types: MessageTypes = {
        EIP712Domain: DOMAIN_TYPE_FIELDS,
        Data: [{ name: 'value', type: `bytes${length}` }],
      };
      const make = (value: unknown): TypedMessage<MessageTypes> => ({
        types: deepClone(types),
        primaryType: 'Data',
        domain: { ...DOMAIN },
        message: { value },
      });

      expectSameEncoding(make(fullHex), make(full), EIP_VERSION_V4);
      expectDifferentMessageEncoding(
        make(fullHex),
        make(shorterHex),
        EIP_VERSION_V4,
      );
    });
  }

  it('pins the exact ABI-like slot layout: left-padded uint, right-padded bytesN, sign-extended int8', () => {
    const types: Record<string, MessageTypeProperty[]> = {
      Data: [
        { name: 'a', type: 'uint8' },
        { name: 'b', type: 'bytes2' },
        { name: 'c', type: 'int8' },
      ],
    };
    const message = { a: 1, b: '0x0203', c: -1 };
    const typeHash = bytesToHex(TypedDataUtils.hashType('Data', types)).slice(
      2,
    );
    const expected = `0x${typeHash}${'00'.repeat(31)}01${'0203'}${'00'.repeat(
      30,
    )}${'ff'.repeat(32)}`;
    expect(
      bytesToHex(
        TypedDataUtils.encodeData('Data', message, types, EIP_VERSION_V4),
      ),
    ).toBe(expected);
  });
});

describe('null policy', () => {
  it('v4: null, undefined and a missing struct field all encode to the zero hash', () => {
    const withNull = mailData();
    withNull.message.optional = null;

    const withUndefined = mailData();
    withUndefined.message.optional = undefined;

    const withMissing = mailData();
    delete withMissing.message.optional;

    expect(digestOf(withUndefined, EIP_VERSION_V4)).toBe(
      digestOf(withNull, EIP_VERSION_V4),
    );
    expect(encodedMessageOf(withUndefined, EIP_VERSION_V4)).toBe(
      encodedMessageOf(withNull, EIP_VERSION_V4),
    );
    expect(digestOf(withMissing, EIP_VERSION_V4)).toBe(
      digestOf(withNull, EIP_VERSION_V4),
    );
    expect(encodedMessageOf(withMissing, EIP_VERSION_V4)).toBe(
      encodedMessageOf(withNull, EIP_VERSION_V4),
    );
  });

  it('v4: a real struct value encodes differently from the null zero-hash slot', () => {
    const withNull = mailData();
    withNull.message.optional = null;
    const withPerson = mailData();
    withPerson.message.optional = {
      name: 'Somebody',
      wallet: '0x0000000000000000000000000000000000000001',
    };
    expectDifferentMessageEncoding(withNull, withPerson, EIP_VERSION_V4);
  });

  it('v4: null is rejected for atomic (non-struct) fields', () => {
    const data = mailData();
    data.message.small = null;
    expect(() => digestOf(data, EIP_VERSION_V4)).toThrow(
      'Unable to encode value',
    );
  });

  it('v3: a null struct field is not silently encoded as a zero hash', () => {
    const data = flatData();
    data.message.from = null;
    expect(() => digestOf(data, EIP_VERSION_V3)).toThrow(TypeError);
  });
});

describe('recursive types', () => {
  const linkedListTypes: MessageTypes = {
    EIP712Domain: DOMAIN_TYPE_FIELDS,
    Node: [
      { name: 'tag', type: 'uint8' },
      { name: 'label', type: 'string' },
      { name: 'next', type: 'Node' },
    ],
  };

  const linkedListMessage = {
    tag: 1,
    label: 'root',
    next: {
      tag: 2,
      label: 'middle',
      next: {
        tag: 3,
        label: 'leaf',
        next: null,
      },
    },
  };

  /**
   * Build a fresh self-recursive linked-list message.
   *
   * @returns A typed message over the self-referential `Node` type.
   */
  function linkedListData(): TypedMessage<MessageTypes> {
    return {
      types: deepClone(linkedListTypes),
      primaryType: 'Node',
      domain: { ...DOMAIN },
      message: deepClone(linkedListMessage),
    };
  }

  it('v4: a self-recursive type hash follows EIP-712 dependency collection', () => {
    expect(TypedDataUtils.encodeType('Node', linkedListTypes)).toBe(
      'Node(uint8 tag,string label,Node next)',
    );
  });

  it('v4: key reordering preserves digest of a self-recursive message', () => {
    const base = linkedListData();
    expectSameEncoding(
      base,
      reorderMessageKeys(reorderTypesObjectKeys(deepClone(base))),
      EIP_VERSION_V4,
    );
  });

  it('v4: field order change alters digest of a self-recursive message', () => {
    const base = linkedListData();
    const variant = swapDeclaredFields(deepClone(base), 'Node', 0, 1);
    expectDifferentMessageEncoding(base, variant, EIP_VERSION_V4);
  });

  it('v4: a single value bit flip in a nested node alters digest', () => {
    const base = linkedListData();
    const variant = deepClone(base);
    setAtPath(variant.message, ['next', 'next', 'tag'], 4);
    expectDifferentMessageEncoding(base, variant, EIP_VERSION_V4);
  });

  const mutualTypes: MessageTypes = {
    EIP712Domain: DOMAIN_TYPE_FIELDS,
    A: [
      { name: 'x', type: 'uint8' },
      { name: 'b', type: 'B' },
    ],
    B: [{ name: 'a', type: 'A' }],
  };

  /**
   * Build a fresh mutually recursive A/B message.
   *
   * @returns A typed message over the mutually recursive `A`/`B` types.
   */
  function mutualData(): TypedMessage<MessageTypes> {
    return {
      types: deepClone(mutualTypes),
      primaryType: 'A',
      domain: { ...DOMAIN },
      message: {
        x: 1,
        b: {
          a: {
            x: 2,
            b: null,
          },
        },
      },
    };
  }

  it('v4: mutually recursive types encode and tolerate key reordering', () => {
    expect(TypedDataUtils.encodeType('A', mutualTypes)).toBe(
      'A(uint8 x,B b)B(A a)',
    );
    const base = mutualData();
    expectSameEncoding(
      base,
      reorderTypesObjectKeys(deepClone(base)),
      EIP_VERSION_V4,
    );
  });

  it('v4: a value change inside mutual recursion alters digest and bytes', () => {
    const base = mutualData();
    const variant = deepClone(base);
    setAtPath(variant.message, ['b', 'a', 'x'], 3);
    expectDifferentMessageEncoding(base, variant, EIP_VERSION_V4);
  });
});

describe('encoder mutation negative controls', () => {
  /*
   * Each test below constructs what a plausible buggy encoder would emit and
   * asserts the fixture distinguishes it from the canonical bytes produced by
   * the real implementation. The canonical type hashes come from the library
   * under test; the rest of the preimage is assembled per the EIP-712 rules.
   */

  it('dependency sorting by types-object declaration order diverges from canonical sorting', () => {
    const types: MessageTypes = {
      EIP712Domain: DOMAIN_TYPE_FIELDS,
      Zebra: [{ name: 'a', type: 'address' }],
      Alpha: [{ name: 'z', type: 'uint8' }],
      Mail: [
        { name: 'z', type: 'Zebra' },
        { name: 'a', type: 'Alpha' },
      ],
    };

    // Buggy variant: dependencies emitted in types-object declaration order.
    /**
     * Encode a type the buggy way, sorting dependencies by their position in
     * the `types` object instead of alphabetically.
     *
     * @param primaryType - The root type to encode.
     * @param allTypes - All type declarations.
     * @returns The mutant's type encoding string.
     */
    function encodeTypeWithDeclarationOrder(
      primaryType: string,
      allTypes: Record<string, MessageTypeProperty[]>,
    ): string {
      const deps = TypedDataUtils.findTypeDependencies(primaryType, allTypes);
      deps.delete(primaryType);
      const declarationIndex = new Map(
        Object.keys(allTypes).map((name, index) => [name, index]),
      );
      const orderedDeps = [...deps].sort(
        (left, right) =>
          (declarationIndex.get(left) ?? 0) -
          (declarationIndex.get(right) ?? 0),
      );
      return [primaryType, ...orderedDeps]
        .map(
          (name) =>
            `${name}(${allTypes[name]
              .map((field) => `${field.type} ${field.name}`)
              .join(',')})`,
        )
        .join('');
    }

    const canonical = TypedDataUtils.encodeType('Mail', types);
    expect(canonical).toBe(
      'Mail(Zebra z,Alpha a)Alpha(uint8 z)Zebra(address a)',
    );
    const declarationOrdered = encodeTypeWithDeclarationOrder('Mail', types);
    expect(declarationOrdered).toBe(
      'Mail(Zebra z,Alpha a)Zebra(address a)Alpha(uint8 z)',
    );
    expect(declarationOrdered).not.toBe(canonical);

    // Canonical sorting is insensitive to the declaration order, so the
    // digest invariants above fail for this mutant on this very fixture.
    const reorderedTypes = Object.fromEntries(
      Object.entries(types).reverse(),
    ) as MessageTypes;
    expect(TypedDataUtils.encodeType('Mail', reorderedTypes)).toBe(canonical);
  });

  it('an array encoding missing its inner keccak layer diverges in length from canonical bytes', () => {
    const types: MessageTypes = {
      EIP712Domain: DOMAIN_TYPE_FIELDS,
      Data: [{ name: 'items', type: 'uint16[]' }],
    };
    const message = { items: [1, 2, 3] };
    const data: TypedMessage<MessageTypes> = {
      types: deepClone(types),
      primaryType: 'Data',
      domain: { ...DOMAIN },
      message: deepClone(message),
    };

    const typeHash = TypedDataUtils.hashType('Data', types);
    const arrayElementTypes = ['uint256', 'uint256', 'uint256'] as const;
    const arrayValues = [BigInt(1), BigInt(2), BigInt(3)] as const;
    const canonicalSlot = keccak256(
      encode([...arrayElementTypes], [...arrayValues]),
    );
    const canonicalBytes = bytesToHex(concatBytes([typeHash, canonicalSlot]));

    // Buggy variant: raw ABI elements concatenated into the slot, no hash.
    const buggySlot = encode([...arrayElementTypes], [...arrayValues]);
    const buggyBytes = bytesToHex(concatBytes([typeHash, buggySlot]));

    expect(encodedMessageOf(data, EIP_VERSION_V4)).toBe(canonicalBytes);
    expect(buggyBytes).not.toBe(canonicalBytes);
    expect(buggySlot).not.toHaveLength(canonicalSlot.length);

    // And array order mutation changes the canonical digest on this fixture,
    // which the one-layer-too-short encoder would not hash per element.
    const swapped = deepClone(data);
    swapped.message.items = [3, 2, 1];
    expectDifferentMessageEncoding(data, swapped, EIP_VERSION_V4);
  });

  it('wrong signed integer extension (magnitude without sign bit) diverges for int8/int256', () => {
    // [type, value, sign-extended 32-byte slot tail, zero-extended magnitude tail]
    const cases: [string, bigint, string, string][] = [
      ['int8', BigInt(-1), 'ff'.repeat(32), `${'00'.repeat(31)}01`],
      ['int8', BigInt(-128), `${'ff'.repeat(31)}80`, `${'00'.repeat(31)}80`],
      ['int256', BigInt(-1), 'ff'.repeat(32), `${'00'.repeat(31)}01`],
    ];

    cases.forEach(([type, value, canonicalTail, magnitudeTail]) => {
      const types: Record<string, MessageTypeProperty[]> = {
        Data: [{ name: 'value', type }],
      };
      const message = { value };
      const typeHash = bytesToHex(TypedDataUtils.hashType('Data', types)).slice(
        2,
      );

      const canonical = bytesToHex(
        TypedDataUtils.encodeData('Data', message, types, EIP_VERSION_V4),
      );
      const canonicalExpected = `0x${typeHash}${canonicalTail}`;
      const magnitudeWithoutSignExtension = `0x${typeHash}${magnitudeTail}`;

      expect(canonical).toBe(canonicalExpected);
      expect(magnitudeWithoutSignExtension).not.toBe(canonical);
    });
  });
});

describe('fixed-seed bounded type-graph fuzzing', () => {
  /*
   * A deterministic PRNG (mulberry32, fixed seed) builds bounded type graphs
   * with structs (self/mutual recursion possible), dynamic and fixed arrays
   * (including one nesting level), atomic extremes and null struct leaves
   * (V4 only). The same metamorphic relations are applied to every generated
   * schema. On failure the generator bounds are shrunk deterministically and
   * the smallest reproducing schema, message and relation paths are reported.
   */

  type Bounds = {
    maxStructs: number;
    maxFields: number;
    maxDepth: number;
    maxArrayLength: number;
  };

  const FULL_BOUNDS: Bounds = {
    maxStructs: 5,
    maxFields: 5,
    maxDepth: 3,
    maxArrayLength: 3,
  };

  const SHRINK_LADDER: Bounds[] = [
    { maxStructs: 2, maxFields: 2, maxDepth: 1, maxArrayLength: 2 },
    { maxStructs: 3, maxFields: 3, maxDepth: 2, maxArrayLength: 2 },
    FULL_BOUNDS,
  ];

  const FUZZ_SEED = 0x71204;
  const FUZZ_CASE_COUNT = 24;

  const ATOMIC_TYPES = [
    'bool',
    'address',
    'string',
    'bytes',
    'bytes1',
    'bytes4',
    'bytes32',
    'uint8',
    'uint32',
    'uint256',
    'int8',
    'int64',
    'int256',
  ];

  type Random = () => number;

  /**
   * Deterministic 32-bit PRNG used to make generation reproducible.
   *
   * @param seed - The fixed PRNG seed.
   * @returns A function producing numbers in the half-open range [0, 1).
   */
  function mulberry32(seed: number): Random {
    // Bitwise operations are the PRNG implementation itself.
    /* eslint-disable no-bitwise, operator-assignment */
    let state = seed >>> 0;
    return () => {
      state = (state + 0x6d2b79f5) | 0;
      let t = Math.imul(state ^ (state >>> 15), 1 | state);
      t = (t + Math.imul(t ^ (t >>> 7), 61 | t)) ^ t;
      return ((t ^ (t >>> 14)) >>> 0) / 4294967296;
    };
    /* eslint-enable no-bitwise, operator-assignment */
  }

  /**
   * Check whether a Solidity type string denotes an array.
   *
   * @param type - The type string.
   * @returns Whether the type ends with an array suffix.
   */
  function isArrayType(type: string): boolean {
    return type.endsWith(']');
  }

  /**
   * Strip one trailing array suffix from a Solidity type string.
   *
   * @param type - The type string.
   * @returns The element/base type without its trailing array suffix.
   */
  function baseType(type: string): string {
    return type.replace(/\[.*\]$/u, '');
  }

  /**
   * Generate one bounded typed-data schema and matching message.
   *
   * @param seed - The PRNG seed identifying the generated case.
   * @param bounds - Upper bounds on graph size, depth and array length.
   * @returns The generated typed message plus its V3 compatibility flag.
   */
  function generateTypedData(
    seed: number,
    bounds: Bounds,
  ): TypedMessage<MessageTypes> & { v3Compatible: boolean } {
    const random: Random = mulberry32(seed);
    const choose = <T>(items: T[]): T =>
      items[Math.floor(random() * items.length)];
    const randomBytes = (length: number): Uint8Array =>
      Uint8Array.from({ length }, () => Math.floor(random() * 256));

    const structCount = 2 + Math.floor(random() * (bounds.maxStructs - 1));
    const structNames = Array.from(
      { length: structCount },
      (_, index) => `S${index}`,
    );

    const fieldDeclarations: Record<string, MessageTypeProperty[]> = {};

    /**
     * Generate one random field type: atomic, struct reference or array.
     *
     * @returns A random valid Solidity/EIP-712 type string.
     */
    function randomFieldType(): string {
      const roll = random();
      if (roll < 0.55) {
        return choose(ATOMIC_TYPES);
      }
      if (roll < 0.75) {
        return choose(structNames);
      }
      const elementType =
        random() < 0.35 ? choose(structNames) : choose(ATOMIC_TYPES);
      const fixedLength =
        2 + Math.floor(random() * (bounds.maxArrayLength - 1));
      const outer = random() < 0.5 ? '[]' : `[${fixedLength}]`;
      if (random() < 0.25) {
        // One level of nested fixed array, e.g. `uint8[2][3]`.
        return `${elementType}[${fixedLength}]${outer}`;
      }
      return `${elementType}${outer}`;
    }

    for (const name of structNames) {
      const fieldCount = 2 + Math.floor(random() * (bounds.maxFields - 1));
      fieldDeclarations[name] = [];
      for (let index = 0; index < fieldCount; index += 1) {
        fieldDeclarations[name].push({
          name: `f${index}`,
          type: randomFieldType(),
        });
      }
    }

    // Guarantee fields exercising every relation (ints, fixed array, struct
    // references and a potentially-nullable struct field).
    fieldDeclarations.S0.push(
      { name: 'gInt', type: 'int256' },
      { name: 'gNeg', type: 'int8' },
      { name: 'gArr', type: 'uint16[2]' },
      { name: 'gStruct', type: 'S1' },
      { name: 'gOpt', type: 'S1' },
    );

    const atomicValue = (type: string): unknown => {
      if (type === 'bool') {
        return random() < 0.5;
      }
      if (type === 'address') {
        return bytesToHex(randomBytes(20));
      }
      if (type === 'string') {
        return choose(['', 'a', 'hello', 'metamorphic', 'unicode-🚀']);
      }
      if (type === 'bytes') {
        return bytesToHex(randomBytes(Math.floor(random() * 8)));
      }
      if (type.startsWith('bytes')) {
        return bytesToHex(randomBytes(Number(type.slice(5))));
      }
      if (type.startsWith('uint')) {
        const bits = Number(type.slice(4));
        const roll = random();
        if (roll < 0.12) {
          return BigInt(0);
        }
        if (roll < 0.24) {
          // eslint-disable-next-line no-bitwise -- shifts construct 2^bits in the value generator
          return (BigInt(1) << BigInt(bits)) - BigInt(1);
        }
        return BigInt(Math.floor(random() * 2 ** Math.min(bits, 20)));
      }
      if (type.startsWith('int')) {
        const bits = Number(type.slice(3));
        // eslint-disable-next-line no-bitwise -- shifts construct 2^(bits-1) in the value generator
        const half = BigInt(1) << BigInt(bits - 1);
        const roll = random();
        if (roll < 0.12) {
          return -half;
        }
        if (roll < 0.24) {
          return half - BigInt(1);
        }
        const magnitude = BigInt(
          Math.floor(random() * 2 ** Math.min(bits - 1, 20)),
        );
        return random() < 0.5 ? magnitude : -magnitude;
      }
      throw new Error(`Unsupported atomic type in fuzzer: ${type}`);
    };

    const valueFor = (type: string, depth: number): unknown => {
      if (fieldDeclarations[type] !== undefined) {
        if (depth >= bounds.maxDepth) {
          return null;
        }
        return Object.fromEntries(
          fieldDeclarations[type].map((field) => [
            field.name,
            valueFor(field.type, depth + 1),
          ]),
        );
      }
      const match = type.match(/^(.*)\[(\d*)\]$/u);
      if (match) {
        const [, elementType, lengthString] = match;
        const length =
          lengthString === ''
            ? 2 + Math.floor(random() * (bounds.maxArrayLength - 1))
            : Number(lengthString);
        return Array.from({ length }, () => valueFor(elementType, depth + 1));
      }
      return atomicValue(type);
    };

    // Insert structs into the types object in a random declaration order so
    // that declaration order is independently exercised.
    const declarationOrder = [...structNames];
    for (let index = declarationOrder.length - 1; index > 0; index -= 1) {
      const swapIndex = Math.floor(random() * (index + 1));
      [declarationOrder[index], declarationOrder[swapIndex]] = [
        declarationOrder[swapIndex],
        declarationOrder[index],
      ];
    }
    const types: MessageTypes = { EIP712Domain: DOMAIN_TYPE_FIELDS };
    for (const name of declarationOrder) {
      types[name] = fieldDeclarations[name];
    }
    // The nullable field is null about half the time (V4 zero-hash slot).
    const message = valueFor('S0', 0) as Record<string, unknown>;
    // Guarantee a negative signed integer so sign-extension mutants are seen.
    message.gNeg = BigInt(-128);
    if (random() < 0.5) {
      message.gOpt = null;
    }

    const usesArrays = Object.values(types).some((fields) =>
      fields.some((field) => isArrayType(field.type)),
    );
    const hasRecursion = (() => {
      const visiting = new Set<string>();
      const visited = new Set<string>();
      const visit = (name: string): boolean => {
        if (visiting.has(name)) {
          return true;
        }
        if (visited.has(name)) {
          return false;
        }
        visiting.add(name);
        for (const field of types[name]) {
          const referenced = baseType(field.type);
          if (types[referenced] !== undefined && visit(referenced)) {
            return true;
          }
        }
        visiting.delete(name);
        visited.add(name);
        return false;
      };
      return structNames.some(visit);
    })();
    const containsNull = (value: unknown): boolean => {
      if (value === null) {
        return true;
      }
      if (Array.isArray(value)) {
        return value.some(containsNull);
      }
      if (value !== null && typeof value === 'object') {
        return Object.values(value).some(containsNull);
      }
      return false;
    };

    const data: TypedMessage<MessageTypes> = {
      types,
      primaryType: 'S0',
      domain: {
        name: 'FuzzDomain',
        version: '1',
        chainId: 1,
        verifyingContract: bytesToHex(randomBytes(20)),
      },
      message,
    };

    // V3 has no arrays/recursion and throws on null struct leaves.
    return {
      ...data,
      v3Compatible: !usesArrays && !hasRecursion && !containsNull(message),
    };
  }

  /**
   * Run every metamorphic relation against one generated case.
   *
   * @param seed - The PRNG seed identifying the generated case.
   * @param bounds - Upper bounds used when generating the case.
   * @returns Human-readable descriptions of the relations that failed.
   */
  function checkGeneratedCase(seed: number, bounds: Bounds): string[] {
    const generated = generateTypedData(seed, bounds);
    const { v3Compatible, ...baseData } = generated;
    const failures: string[] = [];

    const check = (relation: string, assertion: () => void): void => {
      try {
        assertion();
      } catch (error) {
        failures.push(
          `${relation} -> ${(error as Error).message.split('\n')[0]}`,
        );
      }
    };

    const versions: Version[] = [EIP_VERSION_V4];
    if (v3Compatible) {
      versions.push(EIP_VERSION_V3);
    }

    for (const version of versions) {
      const base = deepClone(baseData);
      const baseDigest = digestOf(base, version);
      const baseEncoded = encodedMessageOf(base, version);
      const baseDomainHash = domainHashOf(base, version);

      check(`${version}@types-object-key-reorder`, () => {
        const variant = reorderTypesObjectKeys(deepClone(base));
        expect(encodedMessageOf(variant, version)).toBe(baseEncoded);
        expect(digestOf(variant, version)).toBe(baseDigest);
      });

      check(`${version}@message-property-reorder`, () => {
        const variant = reorderMessageKeys(deepClone(base));
        expect(encodedMessageOf(variant, version)).toBe(baseEncoded);
        expect(digestOf(variant, version)).toBe(baseDigest);
      });

      check(`${version}@add-unrelated-types`, () => {
        const variant = withUnrelatedTypes(deepClone(base));
        expect(encodedMessageOf(variant, version)).toBe(baseEncoded);
        expect(digestOf(variant, version)).toBe(baseDigest);
      });

      check(`${version}@equivalent-value-encodings`, () => {
        const variant = deepClone(base);
        // Guaranteed present by the generator: gInt (int256) and the domain.
        setAtPath(
          variant.message,
          ['gInt'],
          String(getAtPath(base.message, ['gInt'])),
        );
        (variant.domain as any).chainId = '1';
        (variant.domain as any).verifyingContract = swapHexCase(
          (base.domain as any).verifyingContract as string,
        );
        expect(encodedMessageOf(variant, version)).toBe(baseEncoded);
        expect(digestOf(variant, version)).toBe(baseDigest);
      });

      check(`${version}@field-declaration-order@types.S0[f0]/[f1]`, () => {
        const variant = swapDeclaredFields(deepClone(base), 'S0', 0, 1);
        expect(encodedMessageOf(variant, version)).not.toBe(baseEncoded);
        expect(digestOf(variant, version)).not.toBe(baseDigest);
      });

      check(`${version}@primary-type-rename@S0`, () => {
        const variant = renameType(deepClone(base), 'S0', 'Zprimary');
        expect(encodedMessageOf(variant, version)).not.toBe(baseEncoded);
        expect(digestOf(variant, version)).not.toBe(baseDigest);
      });

      check(`${version}@array-element-order@message.gArr`, () => {
        const variant = deepClone(base);
        const arrayPath: Path = ['gArr'];
        const array = getAtPath(variant.message, arrayPath) as unknown[];
        [array[0], array[1]] = [array[1], array[0]];
        expect(encodedMessageOf(variant, version)).not.toBe(baseEncoded);
        expect(digestOf(variant, version)).not.toBe(baseDigest);
      });

      check(`${version}@domain-chainId@domain.chainId`, () => {
        const variant = deepClone(base);
        (variant.domain as any).chainId = 2;
        expect(domainHashOf(variant, version)).not.toBe(baseDomainHash);
        expect(digestOf(variant, version)).not.toBe(baseDigest);
      });

      check(`${version}@single-value-bitflip@message.gInt`, () => {
        const variant = deepClone(base);
        const original = getAtPath(base.message, ['gInt']) as bigint;
        // eslint-disable-next-line no-bitwise -- flipping the low bit is the mutation under test
        setAtPath(variant.message, ['gInt'], original ^ BigInt(1));
        // eslint-disable-next-line no-bitwise -- flipping the low bit is the mutation under test
        expect(original ^ BigInt(1)).not.toBe(original);
        expect(encodedMessageOf(variant, version)).not.toBe(baseEncoded);
        expect(digestOf(variant, version)).not.toBe(baseDigest);
      });

      // Sign extension: int8 -128 occupies a full 32-byte slot
      // (0xff..ff80), not its zero-extended magnitude (0x00..0080).
      check(`${version}@signed-extension@message.gNeg`, () => {
        const variant = deepClone(base);
        setAtPath(variant.message, ['gNeg'], BigInt(-128).toString(10));
        expect(encodedMessageOf(variant, version)).toBe(baseEncoded);
        expect(digestOf(variant, version)).toBe(baseDigest);

        // Canonical slot oracle: sign-extended two's complement bytes.
        const signedTypes = {
          Data: [{ name: 'value', type: 'int8' }],
        };
        const signedEncoded = bytesToHex(
          TypedDataUtils.encodeData(
            'Data',
            { value: BigInt(-128) },
            signedTypes,
            version,
          ),
        );
        const signedTypeHash = bytesToHex(
          TypedDataUtils.hashType('Data', signedTypes),
        );
        expect(signedEncoded).toBe(`${signedTypeHash}${'ff'.repeat(31)}80`);

        // int8 -128 must not share a slot with uint8 128 (0x00..0080).
        const unsignedTypes = {
          Data: [{ name: 'value', type: 'uint8' }],
        };
        const unsignedEncoded = bytesToHex(
          TypedDataUtils.encodeData(
            'Data',
            { value: 128 },
            unsignedTypes,
            version,
          ),
        );
        expect(unsignedEncoded).not.toBe(signedEncoded);
      });
    }

    return failures;
  }

  /**
   * Shrink one failing case deterministically and format its report.
   *
   * @param seed - The seed of the failing case.
   * @param failures - The relations that failed under the full bounds.
   * @returns A formatted report, or null when no shrink reproduces it.
   */
  function buildFailureReport(seed: number, failures: string[]): string | null {
    const smaller = SHRINK_LADDER.map((candidateBounds) => ({
      candidateBounds,
      candidateFailures: checkGeneratedCase(seed, candidateBounds),
    })).filter((entry) => entry.candidateFailures.length > 0);
    const shrunk = smaller[0] ?? {
      candidateBounds: FULL_BOUNDS,
      candidateFailures: failures,
    };
    const minimal = generateTypedData(seed, shrunk.candidateBounds);
    return [
      `seed=0x${seed.toString(16)} bounds=${JSON.stringify(
        shrunk.candidateBounds,
      )}`,
      ...shrunk.candidateFailures,
      JSON.stringify(
        minimal,
        (_key, value) =>
          typeof value === 'bigint' ? value.toString(10) : value,
        2,
      ),
    ].join('\n');
  }

  /**
   * Generate all fixed-seed cases and collect their (shrunk) failure reports.
   *
   * @returns One formatted report per failing seed.
   */
  function collectFailureReports(): string[] {
    const seeds = Array.from(
      { length: FUZZ_CASE_COUNT },
      (_, index) => FUZZ_SEED + index,
    );
    return seeds
      .map((seed) => ({
        seed,
        failures: checkGeneratedCase(seed, FULL_BOUNDS),
      }))
      .filter((entry) => entry.failures.length > 0)
      .map((entry) => buildFailureReport(entry.seed, entry.failures) as string);
  }

  it('holds across all generated bounded type graphs', () => {
    expect(collectFailureReports()).toStrictEqual([]);
  });
});

describe('sign and recover roundtrip on a fixed key', () => {
  it('v4: signs and recovers the fixed signer, and equivalent encodings recover identically', () => {
    const data = mailData();
    const signature = signTypedData({
      privateKey: PRIVATE_KEY,
      data,
      version: EIP_VERSION_V4,
    });
    expect(
      recoverTypedSignature({
        data,
        signature,
        version: EIP_VERSION_V4,
      }),
    ).toBe(SIGNER_ADDRESS);

    const equivalent = mailData();
    equivalent.message.small = '-128';
    equivalent.message.big = INT256_MIN.toString(10);
    (equivalent.domain as any).chainId = '0x1';
    (equivalent.message.from as any).wallet = (
      equivalent.message.from as any
    ).wallet.toLowerCase();
    const equivalentSignature = signTypedData({
      privateKey: PRIVATE_KEY,
      data: equivalent,
      version: EIP_VERSION_V4,
    });
    // Deterministic (RFC 6979) ECDSA over the same digest yields the same
    // signature; recovery of both signatures returns the fixed signer.
    expect(equivalentSignature).toBe(signature);
    expect(
      recoverTypedSignature({
        data: equivalent,
        signature: equivalentSignature,
        version: EIP_VERSION_V4,
      }),
    ).toBe(SIGNER_ADDRESS);
  });

  it('v3: signs and recovers the fixed signer', () => {
    const data = flatData();
    const signature = signTypedData({
      privateKey: PRIVATE_KEY,
      data,
      version: EIP_VERSION_V3,
    });
    expect(
      recoverTypedSignature({
        data,
        signature,
        version: EIP_VERSION_V3,
      }),
    ).toBe(SIGNER_ADDRESS);
  });

  it('v1: signs and recovers the fixed signer', () => {
    const data: TypedDataV1 = [
      { name: 'message', type: 'string', value: 'metamorphic roundtrip' },
    ];
    const signature = signTypedData({
      privateKey: PRIVATE_KEY,
      data,
      version: SignTypedDataVersion.V1,
    });
    expect(
      recoverTypedSignature({
        data,
        signature,
        version: SignTypedDataVersion.V1,
      }),
    ).toBe(SIGNER_ADDRESS);
  });
});
