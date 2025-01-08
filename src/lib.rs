// use bit_vec::BitVec;
// use std::cmp;
use std::io;
use std::fs::File;
use std::io::prelude::{ Read};
use std::io::{BufReader};
use std::path::Path;
// use itertools::Itertools;
const SIGNBIT: i32 = 1 << 31;
type Intervals<'a> = (usize, &'a [usize], usize);
type RegVars<'a> = (u64, usize, &'a mut i64, &'a [i32]);
type P2Vars<'a> = (&'a mut i32, usize);
type S2bVars<'a> = (&'a mut usize, &'a [usize], &'a [i32]);

pub fn int_sqrt(n: usize) -> usize {
    (n as f64).sqrt().floor() as usize
}

#[inline]
pub fn cnt_query(mut pos: usize, counter: &[i32]) -> i64 {
    let mut acc = counter[pos] & !SIGNBIT;
    pos += 1;
    pos &= pos - 1;
    while pos != 0 {
        acc += counter[pos - 1] & !SIGNBIT;
        pos &= pos - 1;
    }
    i64::from(acc)
}

pub fn input() -> u32 {
    println!("Please enter an integer from 1 to 18. The program will count the exact number of primes below this power of 10: ");
    let mut exponent = String::new();
    io::stdin()
        .read_line(&mut exponent)
        .expect("Failed to read line");
    let exponent: u32 = exponent.trim().parse().expect("Please enter an integer");
    match exponent {
        1..=18 => (),
        _ => {
            println!("Not a valid input: integer between 1 and 18");
            return 0;
        }
    }
    exponent
}

pub fn initialize_arrays(
    ll: usize,
    mu: &mut [isize],
    pi: &mut [usize],
    big_primes: &[i32],
) -> usize {
    for j in 2..mu.len() {
        if mu[j] == 1 {
            let mut i = j;
            while i <= ll +1 {
                mu[i] = match mu[i] {
                    1 => 1 - 2 * j as isize,
                    _ => -mu[i],
                };
                i += 2 * j - 1;
            }
        }
    }
    let mut j = 2;
    while j * j <= (ll+1) << 1 {
        if mu[j] == 1 - 2 * j as isize {
            let mut i = 2 * j * j - 2 * j + 1;
            while i <= ll +1 {
                mu[i] = 0;
                i += 4 * j * j - 4 * j + 1;
            }
        }
        j += 1;
    }
    // big_primes[1] = 2;
    let mut pix = 0;
    let mut prime = big_primes[1] as usize;
    for i  in 2..((ll+1)*2) {
        if i == prime {
           pix += 1 ;
            prime = big_primes[pix+1] as usize;
        }
        pi[(i+1)>>1] = pix;
    }
    //println!("{:?}",mu) ;
    pix
}

pub fn ordinary_leaves(n: usize, mu: &[isize], m: &u64) -> i64 {
    let mut result = 0;
    let it = (1..n + 1).filter(|&i| i % 4 != 0);
    it.for_each(|i| {
        if i % 2 == 1 {
            let term = mu[(i + 1) >> 1].signum() as i64;
            result += term * (*m as i64 / i as i64);
        } else {
            let term = mu[((i >> 1) + 1) >> 1].signum() as i64;
            result -= term * (*m as i64 / i as i64);
        }
    });
    result
}

#[inline]
pub fn special_leaves_type_1(intervals: Intervals, reg_var: RegVars, m1b: &mut usize, pp: isize, mu: &[isize], phi_b:i64,) {
    // println!("b= {}, phi = {:?}",b,phi);
    if *m1b % 2 == 0 {
        *m1b -= 1;
    }
    let criterion = reg_var.1 / pp as usize;
    let mut y;
    let mut mu_value ;
    let mut query;
    while *m1b > criterion {
         mu_value = mu[(*m1b + 1) >> 1];
        if  pp < mu_value.abs()  {
         y = (reg_var.0 / (*m1b as u64 * pp as u64)) as usize - intervals.1[intervals.0];
        if y >= intervals.2 { return; } else {
            query = cnt_query(y , reg_var.3);
            *reg_var.2 -= mu_value.signum() as i64 * (phi_b + query );
        }
    }
        *m1b -= 2;
      }
      }

#[inline]
pub fn special_leaves_type_2(index: usize, intervals: Intervals, reg_var: &mut RegVars, s2b_var: &mut S2bVars, tt_index: &mut u8,pp:u64) -> i64 {
    let mut s2_primes = 0;
let term2 = ((reg_var.0/pp) as f64).sqrt().floor() as i32; //careful, this is not i64
    while *s2b_var.0   > index + 1 {
        let mut y = (reg_var.0 / (pp * s2b_var.2[*s2b_var.0] as u64)) as usize;
        let bit_n = y < reg_var.1;
        match tt_index {
            0 => {
                if bit_n {
                    let l = s2b_var.1[(y + 1) >> 1] - index + 1;
                    let term = reg_var.0/(pp * s2b_var.2[index + l] as u64);
                    let d_prime = s2b_var.1[((term + 1) >> 1) as usize];
                    if s2b_var.2[d_prime + 1] <= term2
                        || d_prime <= index
                    {
                        *tt_index = 1;
                        *reg_var.2 += l as i64;
                        *s2b_var.0 -= 1;
                    } else {
                        *reg_var.2 += (l as u32 * (*s2b_var.0 - d_prime) as u32) as i64;
                        *s2b_var.0 = d_prime;
                    }
                } else {
                    // *tt_index = 2u8;
                    return s2_primes;
                    // break;
                }
            },
            1 => {
                if bit_n {
                    let l = s2b_var.1[(y + 1) >> 1] - index + 1;
                    *reg_var.2 += l as i64;
                    *s2b_var.0 -= 1;
                } else {
                    *tt_index = 2;
                    return s2_primes;
                    // break;
                }
            },
            _ => {
             y -= intervals.1[intervals.0];
            if y < intervals.2
                {
                    *reg_var.2 += cnt_query(y, reg_var.3) ;
                    *s2b_var.0 -= 1;
                    s2_primes += 1;
                }
            else {
                return s2_primes;
            // break;
            }
        },
        }
}
    s2_primes
}
pub fn prime_table(size: &str) -> Vec<i32> // size "2" to "9"// or "2e9"
{
    const LOC: &str = "/tmp/ramdisk/";
    // const LOC: &str = "/home/steve/Developer/projects/binary_files/"; // /media/steve/882F-CE8C/";
    const FILE_PREFIX :&str= "paspe";
    const FILE_SUFFIX :&str = "gp.bin";
    // const ALT_FILE_PREFIX : &str = "pcp";
    let mut filename : String = /*if size.len() == 1*/ {FILE_PREFIX.into()}; // else {ALT_FILE_PREFIX.into()};
    filename.push_str(size);
    filename.push_str(FILE_SUFFIX.into());
    let mut filespec : String = LOC.into();
    filespec.push_str(&filename);
    // let filespec = concat!(LOC,FILEPREFIX,size,FILE_SUFFIX);
    println!("filespec = {:?}",filespec);
    let path = Path::new(&filespec);
    let file = match File::open(&path) {
        Ok(file) => file,
        Err(err) => {
            println!("Error while opening file: {}", err);
            panic!();
        }
    };
    let mut ff = BufReader::new(file);
    let mut buf: Vec<u8> = Vec::new();
    let mut pvec = vec![1, 2, 3];
    ff.read_to_end(&mut buf).unwrap();
    let mut prime = 3;
    for i in buf {
        prime += 2 * i32::from(i);
        pvec.push(prime);
    }
    pvec
}

#[inline]
pub fn p2(
    intervals: Intervals,
    reg_var: RegVars,
    mut p2_var: P2Vars,
    // _block: &mut BitVec,
    primes: &[i32],
    a: usize,
) -> (u32, usize) {
    let mut p2primes = 0;
    while *p2_var.0 > reg_var.1 as i32{
        match primes.binary_search(&p2_var.0 ) {
            Ok(_) =>
                {
                    let y = (reg_var.0 / (*p2_var.0 as u64)) as usize;
                    if y < intervals.1[intervals.0 + 1] {
                        *reg_var.2 -=
                            (cnt_query(y - intervals.1[intervals.0], reg_var.3) as usize + a) as i64 - 1;
                        p2primes += 1;
                        p2_var.1 += 1;
                    } else {
                        break;
                    }
                },
            Err(_) =>{},
        };
        *p2_var.0 -= 2;
}
     (p2primes, p2_var.1)
}
