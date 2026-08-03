#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

test_verify_one_file! {
    #[test]
    non_extendible_iterator_trait_bound_cycle verus_code! {
        trait Iter {
            type Item;

            #[verifier::non_extendible_spec]
            fn collect<B>(self)
                where
                    Self: Sized,
                    B: FromIter<Self::Item>,
                ensures
                    true,
            ;
        }

        trait FromIter<A> {
            fn from_iter<T>(_iter: T)
                where
                    T: IntoIter<Item = A>,
            ;
        }

        trait IntoIter {
            type Item;
            type Into: Iter<Item = Self::Item>;
        }
    } => Ok(())
}

// test_verify_one_file! {
//     #[test]
//     overridden_exec_method_ignores_default_ensures verus_code! {
//         trait Iter {
//             type Item;

//             fn collect<B>(self) -> (r: u8)
//                 where
//                     Self: Sized,
//                     B: FromIter<Self::Item>,
//                 default_ensures
//                     r == 0,
//             {
//                 0
//             }
//         }

//         trait FromIter<A> {
//             fn from_iter<T>(_iter: T)
//                 where
//                     T: IntoIter<Item = A>,
//             ;
//         }

//         trait IntoIter {
//             type Item;
//             type Into: Iter<Item = Self::Item>;
//         }

//         struct ConcreteIter;

//         impl Iter for ConcreteIter {
//             type Item = u8;

//             fn collect<B>(self) -> (r: u8)
//                 where
//                     B: FromIter<u8>,
//                 ensures
//                     r == 1,
//             {
//                 1
//             }
//         }
//     } =>  Err(err) => assert_vir_error_msg(
//         err,
//         "found a cyclic self-reference in a definition",
//     )
// }
// test_verify_one_file! {
//     #[test]
//     default_exec_contract_trait_bound_cycle verus_code! {
//         trait Iter {
//             type Item;

//             fn collect<B>(self)
//                 where
//                     Self: Sized,
//                     B: FromIter<Self::Item>,
//                 default_ensures
//                     true,
//             {
//             }
//         }

//         trait FromIter<A> {
//             fn from_iter<T>(_iter: T)
//                 where
//                     T: IntoIter<Item = A>,
//             ;
//         }

//         trait IntoIter {
//             type Item;
//             type Into: Iter<Item = Self::Item>;
//         }
//     } => Ok(())
// }

