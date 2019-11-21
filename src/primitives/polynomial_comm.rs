use curv::elliptic::curves::traits::ECScalar;
use curv::arithmetic::traits::Samplable;
use curv::BigInt;
use curv::FE;
use crate::BinaryQF;
use crate::primitives::numerical_log;
use crate::pari_init;
struct Setup{
    pub group: BinaryQF,
    pub g: BinaryQF,
    pub q: BigInt,
}

impl Setup{
    // d is the rank of the polynomial,
    pub fn pp(d_max: &BigInt) -> Self{
        unsafe { pari_init(10000000, 2) };
        // choose determinant with 1600 bits, which is equivalent to 3072 bit RSA. That I believe is 120bit security now
        let mut det: BigInt;
        let mut flag = false;

        det = -BigInt::sample(1600);


        while det.mod_floor(&BigInt::from(4)) != BigInt::one(){
             det = -BigInt::sample(1600);
        }

        let group = BinaryQF::binary_quadratic_form_principal(&det);

        // sample random number to get a random group element. TODO: make sure sample bit size and method are ok


        let random = BigInt::sample(256);
        let g = group.exp(&random);

        let bound : BigInt = BigInt::from(3) * numerical_log(&(d_max + BigInt::one())) + BigInt::one();
        // not safe
        let bound_u32 = u32::from_str_radix(&bound.to_str_radix(16),16).unwrap();

        let p = BigInt::from(2).pow(256);
        let q = p.pow(bound_u32);
        Setup{
            group,
            g,
            q,
        }
    }
}

pub fn encode(p: &BigInt, q: &BigInt, coef_vec: &[FE]) -> BigInt{
    // notation change to fit the paper:
    // transform the coefficients to integer coefficients bounded [-p/2,p/2]
    let mut coef_vec_int = (0..coef_vec.len()).map(|i|{
        coef_vec[i].to_big_int() - &p.div_floor(&BigInt::from(2))
    }).collect::<Vec<BigInt>>();
    // transform to Z :
    coef_vec_int.reverse();
    let z = coef_vec_int.iter().fold(BigInt::zero(),|acc,x|{
        x + acc * q
    } );
    z
}

pub fn decode(p: &BigInt, q: &BigInt, y: &BigInt) -> Vec<FE>{
    let one = BigInt::one();
    let p_half = p.div_floor(&BigInt::from(2));
    let bits_in_y= BigInt::from(y.to_str_radix(2).len() as u32);
    let bits_in_q = BigInt::from(q.to_str_radix(2).len() as u32);
    let mut d : BigInt = one.clone();
    while &(&d * &bits_in_q) < &bits_in_y {d = d + &one}


    let mut coef_vec: Vec<FE> = Vec::new();
    let mut q_k = BigInt::one();
    let two = BigInt::from(2);
    let one = BigInt::from(1);
    let s_minus_1 = BigInt::zero();
    let mut s_0 = y.mod_floor(q);
    if s_0 > q.div_floor(&two){
      //  s_0 = q - &s_0 - &p_half;
        s_0 = q - &s_0 ;
        s_0 = -s_0 + &p_half;
    }
    else{
        s_0 = &s_0 + &p_half;
    }
    q_k = q_k * q;

    let f_0 = (s_0 - s_minus_1);


    coef_vec.push(ECScalar::from(&f_0));
    if d == one{ return coef_vec;}
    while d > one{
    let mut case = 0;
        let mut s_k_minus_1 = y.mod_floor(&q_k);
        if s_k_minus_1 > q_k.div_floor(&two){
            s_k_minus_1 = &q_k - &s_k_minus_1;
            case = case + 1;
        }
        else{
            case = case + 10;
        }
        let q_k_plus_1 = &q_k * q;
        let mut s_k = y.mod_floor(&q_k_plus_1);
        if &s_k > &(q_k_plus_1.div_floor(&two)){
            s_k = &q_k_plus_1 - &s_k;
            case = case + 100;
        }
        else{
            case = case + 1000;
        }
        let mut f_k = (s_k - s_k_minus_1).div_floor(&q_k);

        match case {
            101 => f_k =  -&f_k + &p_half,
            1001 => f_k = &f_k + &p_half + &one,
            110 => f_k = -&f_k + &p_half - &one,
            1010 => f_k = &f_k + &p_half ,
            _ => println!("error"),// TODO: return an error
        };

        coef_vec.push(ECScalar::from(&f_k));
        q_k = q_k_plus_1;
        d = d - &one;
    }
    return coef_vec
}



#[cfg(test)]
mod tests {
    use curv::BigInt;
    use curv::FE;
    use curv::elliptic::curves::traits::ECScalar;
    use super::{encode,decode};
    use super::Setup;
    use crate::primitives::numerical_log;

    #[test]
    fn test_encode_decode() {

        let p = FE::q();
        // sample coef vector
        let mut coef_vec: Vec<FE>  = Vec::new();
        let mut i = 0;
        while i<9{ // TODO: check that i < d_max
            coef_vec.push(FE::new_random());
            i = i + 1;
        }
        let d_max = BigInt::from(11);
        let pp = Setup::pp(&d_max);
        let z = encode(&p, &pp.q, &coef_vec[..]);

        let coef_vec_dec = decode(&p, &pp.q, &z );

        assert_eq!(coef_vec_dec, coef_vec);

    }


    #[test]
    fn test_encode_decode_toy_example() {

        let p = BigInt::from(20); // apparently the p in the toy example from the paper is too small (problem with doing -p/2)
       // let q = BigInt::from(10);
        let d_max = 10;
        let bound : BigInt = BigInt::from(3) * numerical_log(&(d_max + BigInt::one())) + BigInt::one();
        // not safe
        let bound_u32 = u32::from_str_radix(&bound.to_str_radix(16),16).unwrap();
        let q = p.pow(bound_u32);

        let mut coef_vec: Vec<FE>  = Vec::new();

        coef_vec.push(ECScalar::from(&BigInt::from(2)));
        coef_vec.push(ECScalar::from(&BigInt::from(3)));
        coef_vec.push(ECScalar::from(&BigInt::from(4)));
        coef_vec.push(ECScalar::from(&BigInt::from(1)));

        let z = encode(&p,&q, &coef_vec[..]);

        let coef_vec_dec = decode(&p, &q, &z );

        assert_eq!(coef_vec_dec, coef_vec);

    }


}