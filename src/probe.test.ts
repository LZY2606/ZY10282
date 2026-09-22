import { SignTypedDataVersion, TypedDataUtils } from './sign-typed-data';

const V4 = SignTypedDataVersion.V4;
const V3 = SignTypedDataVersion.V3;
const MIN256 = -(BigInt(2) ** BigInt(255));
const MAX256 = BigInt(2) ** BigInt(255) - BigInt(1);

describe('probe', () => {
  it('bytesN padding', () => {
    const types = { B: [{ name: 'x', type: 'bytes2' }] };
    const a = TypedDataUtils.encodeData('B', { x: '0xab' }, types as any, V4);
    const b = TypedDataUtils.encodeData('B', { x: '0xab00' }, types as any, V4);
    const c = TypedDataUtils.encodeData('B', { x: new Uint8Array([0xab]) }, types as any, V4);
    console.log('bytes2', a.toString('hex'), b.toString('hex'), c.toString('hex'), a.equals(b), a.equals(c));
  });
  it('address case', () => {
    const types = { A: [{ name: 'w', type: 'address' }] };
    const a = TypedDataUtils.encodeData('A', { w: '0xCD2a3d9F938E13CD947Ec05AbC7FE734Df8DD826' }, types as any, V4);
    const b = TypedDataUtils.encodeData('A', { w: '0xcd2a3d9f938e13cd947ec05abc7fe734df8dd826' }, types as any, V4);
    console.log('addr', a.equals(b), a.toString('hex'));
  });
  it('int forms', () => {
    const types = { I: [{ name: 'v', type: 'int8' }, { name: 'w', type: 'int256' }] };
    const base = { v: -128, w: MIN256 };
    for (const variant of [
      base,
      { v: '-128', w: MIN256.toString() },
      { v: BigInt(-128), w: MIN256 },
    ]) {
      console.log('int', TypedDataUtils.encodeData('I', variant as any, types as any, V4).toString('hex'));
    }
    const maxes = { v: 127, w: MAX256 };
    console.log('intmax', TypedDataUtils.encodeData('I', maxes as any, types as any, V4).toString('hex'));
    console.log('intmaxs', TypedDataUtils.encodeData('I', { v: '127', w: MAX256.toString() } as any, types as any, V4).toString('hex'));
  });
  it('null policies', () => {
    const types = { Node: [{ name: 'v', type: 'int256' }, { name: 'next', type: 'Node' }] };
    const m = { v: 1, next: { v: 2, next: null } };
    console.log('nullv4', TypedDataUtils.encodeData('Node', m as any, types as any, V4).toString('hex'));
    const types3 = { M: [{ name: 'a', type: 'int256' }] };
    console.log('v3undef', TypedDataUtils.encodeData('M', { a: 1, b: undefined } as any, types3 as any, V3).toString('hex'));
    console.log('v3plain', TypedDataUtils.encodeData('M', { a: 1 } as any, types3 as any, V3).toString('hex'));
    try {
      TypedDataUtils.encodeData('M', { a: undefined } as any, types3 as any, V4);
    } catch (e: any) { console.log('v4undef throws:', e.message); }
    try {
      TypedDataUtils.encodeData('M', { a: null } as any, types3 as any, V4);
    } catch (e: any) { console.log('v4nullatom throws:', e.message); }
  });
  it('nested/fixed arrays', () => {
    const types = {
      Person: [{ name: 'name', type: 'string' }, { name: 'wallets', type: 'address[2]' }],
      M: [{ name: 'grid', type: 'uint256[2][3]' }, { name: 'people', type: 'Person[2][]' }],
    };
    const m = {
      grid: [[1, 2], [3, 4], [5, 6]],
      people: [
        [
          { name: 'a', wallets: ['0xCD2a3d9F938E13CD947Ec05AbC7FE734Df8DD826', '0x' + 'bb'.repeat(20)] },
          { name: 'b', wallets: ['0xCD2a3d9F938E13CD947Ec05AbC7FE734Df8DD8DD826'.toLowerCase(), '0x' + 'cc'.repeat(20)] },
        ],
      ],
    };
    console.log('nested', TypedDataUtils.encodeData('M', m as any, types as any, V4).toString('hex').length);
  });
  it('deps order', () => {
    const types = {
      Zeta: [{ name: 'z', type: 'int256' }],
      Alpha: [{ name: 'z', type: 'Zeta' }],
      Message: [{ name: 'a', type: 'Alpha' }],
    };
    console.log('dep1', TypedDataUtils.encodeType('Message', types as any));
    const reordered = { Message: types.Message, Alpha: types.Alpha, Zeta: types.Zeta };
    console.log('dep2', TypedDataUtils.encodeType('Message', reordered as any));
  });
  it('eip712 digest domain-only', () => {
    const d = { types: { EIP712Domain: [{ name: 'chainId', type: 'uint256' }] }, primaryType: 'EIP712Domain', domain: { chainId: 1 }, message: {} };
    console.log('domainhash', TypedDataUtils.eip712Hash(d as any, V4).toString('hex'));
  });
});
