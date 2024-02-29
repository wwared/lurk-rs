use crate::coprocessor::gadgets;
use bellpepper::gadgets::multipack::pack_bits;
use bellpepper_bls12381::{
    curves::{g1::G1Point, g2::G2Point, pairing::EmulatedBls12381Pairing},
    fields::fp::FpElement,
    fields::fp12::Fp12Element,
};
use bellpepper_core::{
    boolean::Boolean,
    num::{AllocatedNum, Num},
    test_cs::TestConstraintSystem,
    ConstraintSystem, SynthesisError,
};
use bls12_381::fp::Fp as BlsFp;
use bls12_381::{G1Affine, G1Projective, G2Affine, G2Projective};
use itertools::Itertools;
use lurk_macros::Coproc;
use serde::{Deserialize, Serialize};
use std::marker::PhantomData;

use crate::{
    self as lurk,
    circuit::gadgets::pointer::AllocatedPtr,
    field::LurkField,
    lem::{pointers::Ptr, store::Store},
    tag::{ExprTag, Tag},
    z_ptr::ZPtr,
};

use super::{CoCircuit, Coprocessor};

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct PairingCoprocessor<F: LurkField> {
    pub(crate) _p: PhantomData<F>,
}

impl<F: LurkField> CoCircuit<F> for PairingCoprocessor<F> {
    fn arity(&self) -> usize {
        // FIXME: this should depend on the number of limbs for the particular emulated field params
        // g1 is 7 * 2, g2 is 7 * 2 * 2, gt is 7 * 12
        // taking in 2 g1 elements and 2 g2 elements is the same size as one gt elem!
        // (doesn't particularly matter since output is always a single Ptr)
        2 * (7 * 2 + 7 * 2 * 2)
    }

    #[inline]
    fn synthesize_simple<CS: ConstraintSystem<F>>(
        &self,
        cs: &mut CS,
        g: &lurk::lem::circuit::GlobalAllocator<F>,
        s: &lurk::lem::store::Store<F>,
        not_dummy: &Boolean,
        ptrs: &[AllocatedPtr<F>],
    ) -> Result<AllocatedPtr<F>, SynthesisError> {
        assert_eq!(ptrs.len(), 84);

        let input = ptrs
            .iter()
            .map(|p| p.hash().clone())
            .collect::<Vec<AllocatedNum<F>>>();

        let nums: Vec<Num<F>> = input.into_iter().map(|i| Num::from(i)).collect();

        // g1
        let ax_limbs = &nums[0..7];
        let ay_limbs = &nums[7..14];
        // g2
        let bx_limbs = &nums[14..28];
        let by_limbs = &nums[28..42];
        // g1
        let cx_limbs = &nums[42..49];
        let cy_limbs = &nums[49..56];
        // g2
        let dx_limbs = &nums[56..70];
        let dy_limbs = &nums[70..84];

        use bellpepper_bls12381::curves::pairing::EmulatedPairing;

        let a_alloc = G1Point::from_limbs(&mut cs.namespace(|| "alloc a"), ax_limbs, ay_limbs)?;
        let b_alloc = G2Point::from_limbs(&mut cs.namespace(|| "alloc b"), bx_limbs, by_limbs)?;
        // let aa = G1Affine::from(&a_alloc);
        // let bb = G2Affine::from(&b_alloc);
        // eprintln!("=> {:?}", aa);
        // eprintln!("=> {:?}", bb);
        let p1_alloc = EmulatedBls12381Pairing::pair(
            &mut cs.namespace(|| "pair(a, b)"),
            &[a_alloc],
            &[b_alloc],
        )?;
        let c_alloc = G1Point::from_limbs(&mut cs.namespace(|| "alloc c"), cx_limbs, cy_limbs)?;
        let d_alloc = G2Point::from_limbs(&mut cs.namespace(|| "alloc d"), dx_limbs, dy_limbs)?;
        let p2_alloc = EmulatedBls12381Pairing::pair(
            &mut cs.namespace(|| "pair(c, d)"),
            &[c_alloc],
            &[d_alloc],
        )?;
        let is_equal = p1_alloc.sub(&mut cs.namespace(|| "p1 - p2"), &p2_alloc)?;
        let is_equal = is_equal.alloc_is_zero(&mut cs.namespace(|| "p1 - p2 =? 0"))?;
        let sig_check = pack_bits(
            &mut cs.namespace(|| "bit to num"),
            &[Boolean::from(is_equal)],
        )?;
        AllocatedPtr::alloc_tag(ns!(cs, "output"), ExprTag::Num.to_field(), sig_check)
    }
}

impl<F: LurkField> Coprocessor<F> for PairingCoprocessor<F> {
    fn eval_arity(&self) -> usize {
        //7 * 2 + 7 * 2 * 2
        84
    }

    fn has_circuit(&self) -> bool {
        true
    }

    fn evaluate_simple(&self, s: &Store<F>, ptrs: &[Ptr]) -> Ptr {
        // GROSS: use TestCS here to reuse the conversion functions that already exist
        let mut cs = TestConstraintSystem::<F>::new();
        // TODO: write a function for F -> BigInt and use bellpepper-emulated's recompose instead (or a from_limbs alternative that doesnt use CS)
        let nums = ptrs
            .iter()
            .map(|ptr| s.hash_ptr(ptr).value().clone())
            .collect::<Vec<F>>();
        let nums = nums
            .into_iter()
            .enumerate()
            .map(|(i, n)| {
                Num::from(AllocatedNum::alloc_infallible(
                    &mut cs.namespace(|| format!("{i}")),
                    || n,
                ))
            })
            .collect::<Vec<Num<F>>>();

        // g1
        let ax_limbs = &nums[0..7];
        let ay_limbs = &nums[7..14];
        // g2
        let bx_limbs = &nums[14..28];
        let by_limbs = &nums[28..42];
        // g1
        let cx_limbs = &nums[42..49];
        let cy_limbs = &nums[49..56];
        // g2
        let dx_limbs = &nums[56..70];
        let dy_limbs = &nums[70..84];

        let a_alloc =
            G1Point::from_limbs(&mut cs.namespace(|| "alloc a"), ax_limbs, ay_limbs).unwrap();
        let b_alloc =
            G2Point::from_limbs(&mut cs.namespace(|| "alloc b"), bx_limbs, by_limbs).unwrap();
        let c_alloc =
            G1Point::from_limbs(&mut cs.namespace(|| "alloc c"), cx_limbs, cy_limbs).unwrap();
        let d_alloc =
            G2Point::from_limbs(&mut cs.namespace(|| "alloc d"), dx_limbs, dy_limbs).unwrap();
        let a = G1Affine::from(&a_alloc);
        let b = G2Affine::from(&b_alloc);
        let c = G1Affine::from(&c_alloc);
        let d = G2Affine::from(&d_alloc);
        let p1 = bls12_381::pairing(&a, &b);
        let p2 = bls12_381::pairing(&c, &d);
        let res = if p1 == p2 { F::ONE } else { F::ZERO };
        s.num(res)
        // failed experiments with trying to return a list:
        // let nil = s.intern_nil();
        // s.list([s.list([])])
        // nil
        // ptrs[0]
        // let n = s.num(*hash_zptr);
        // s.list([n])
        // s.list([n])
        // s.list([
        //     n,
        //     n,
        //     n,
        //     n,
        //     n,
        // ])
        // args[0].clone()
        // let z_ptrs = args.iter().map(|ptr| s.hash_ptr(ptr)).collect::<Vec<_>>();
        // s.num(compute_pairing(&z_ptrs))
    }
}

impl<F: LurkField> PairingCoprocessor<F> {
    pub fn new(n: usize) -> Self {
        Self {
            _p: Default::default(),
        }
    }
}

#[derive(Clone, Debug, Coproc, Serialize, Deserialize)]
pub enum PairingCoproc<F: LurkField> {
    SC(PairingCoprocessor<F>),
}
