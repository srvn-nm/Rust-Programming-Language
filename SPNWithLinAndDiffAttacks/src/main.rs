// PRESENT S-box (4-bit to 4-bit)
const SBOX: [u8; 16] = [
    0xC, 0x5, 0x6, 0xB, 0x9, 0x0, 0xA, 0xD, 
    0x3, 0xE, 0xF, 0x8, 0x4, 0x7, 0x1, 0x2,
];

// Inverse PRESENT S-box
const SBOX_INV: [u8; 16] = [
    0x5, 0xE, 0xF, 0x8, 0xC, 0x1, 0x2, 0xD, 
    0xB, 0x4, 0x6, 0x3, 0x0, 0x7, 0x9, 0xA,
];

/// Apply the S-box to each nibble (4-bit chunk) in a 16-bit word
fn sbox_layer(state: u16) -> u16 {
    let mut output = 0;
    for i in 0..4 {
        let nibble = (state >> (i * 4)) as u8 & 0xF;
        let substituted = SBOX[nibble as usize] as u16;
        output |= substituted << (i * 4);
    }
    output
}

/// Apply the inverse S-box to each nibble in a 16-bit word
fn sbox_inv_layer(state: u16) -> u16 {
    let mut output = 0;
    for i in 0..4 {
        let nibble = (state >> (i * 4)) as u8 & 0xF;
        let substituted = SBOX_INV[nibble as usize] as u16;
        output |= substituted << (i * 4);
    }
    output
}

/// Bit permutation (transposition of a 4x4 bit matrix)
fn pbox(state: u16) -> u16 {
    let mut output = 0;
    // Transpose bits: original bit i goes to position (i % 4) * 4 + (i / 4)
    for i in 0..16 {
        let bit = (state >> i) & 1;
        let j = (i % 4) * 4 + (i / 4);
        output |= bit << j;
    }
    output
}

/// Generate round keys from a master key (80 bits stored in u128)
fn expand_key(master_key: u128, rounds: usize) -> Vec<u16> {
    (0..rounds).map(|i| {
        // Extract 16-bit chunks from the master key (shift right by 64, 48, 32, 16, 0 bits)
        (master_key >> (80 - 16 * (i + 1))) as u16
    }).collect()
}

/// Encrypt a 16-bit block using the SPN
fn encrypt(plaintext: u16, round_keys: &[u16]) -> u16 {
    let mut state = plaintext;
    // Initial whitening
    state ^= round_keys[0];
    
    // Rounds 1 to 3: S-box, P-box, XOR round key
    for i in 1..4 {
        state = sbox_layer(state);
        state = pbox(state);
        state ^= round_keys[i];
    }
    
    // Final round: S-box and last key XOR (no P-box)
    state = sbox_layer(state);
    state ^= round_keys[4];
    state
}

/// Decrypt a 16-bit block using the SPN
fn decrypt(ciphertext: u16, round_keys: &[u16]) -> u16 {
    let mut state = ciphertext;
    // Reverse final round
    state ^= round_keys[4];
    state = sbox_inv_layer(state);
    
    // Rounds 3 to 1: XOR round key, inverse P-box, inverse S-box
    for i in (1..4).rev() {
        state ^= round_keys[i];
        state = pbox(state); // P-box is its own inverse
        state = sbox_inv_layer(state);
    }
    
    // Reverse initial whitening
    state ^= round_keys[0];
    state
}

// Linear Attack Implementation
// ----------------------------

/// Compute the bias of a linear approximation for the S-box
/// `a`: input mask (4 bits), `b`: output mask (4 bits)
/// Returns: bias = (count_matches / 16.0) - 0.5
fn linear_bias_sbox(a: u8, b: u8) -> f32 {
    let mut count = 0;
    for x in 0..16 {
        // Compute <a, x> and <b, sbox(x)>
        let input_dot = (a as u16 & x).count_ones() % 2;
        let output_dot = (b as u16 & SBOX[x as usize] as u16).count_ones() % 2;
        if input_dot == output_dot {
            count += 1;
        }
    }
    (count as f32 / 16.0) - 0.5
}

/// Perform a linear attack to recover part of the last round key
/// `pairs`: vector of (plaintext, ciphertext) pairs
/// `alpha`: input mask for plaintext
/// `beta`: mask for the input to the last S-box layer
/// `nibble_idx`: which nibble (0-3) of the last round key to attack
/// Returns: candidate key nibble with the highest bias magnitude
fn linear_attack(pairs: &[(u16, u16)], alpha: u16, beta: u16, nibble_idx: usize) -> u8 {
    // Shift beta to align with the target nibble
    let beta_nibble = ((beta >> (4 * nibble_idx)) & 0xF) as u8;
    let mut counts = [0; 16]; // Counts for each candidate key nibble (0-15)
    
    for (plain, cipher) in pairs {
        // Plaintext linear part: <alpha, plain>
        let alpha_dot = (alpha & *plain).count_ones() % 2;
        
        // Test each candidate key for the target nibble
        for candidate in 0..16 {
            // Extract target ciphertext nibble and XOR candidate key
            let cipher_nibble = (cipher >> (4 * nibble_idx)) & 0xF;
            let u = cipher_nibble ^ candidate as u16;
            // Apply inverse S-box to the nibble
            let v = SBOX_INV[u as usize] as u16;
            // Compute <beta_nibble, v>
            let beta_dot = (beta_nibble as u16 & v).count_ones() % 2;
            
            // Check if linear approximation holds (mod 2)
            if (alpha_dot + beta_dot) % 2 == 0 {
                counts[candidate as usize] += 1;
            }
        }
    }
    
    // Find candidate with bias closest to expected (max deviation from 50%)
    let total = pairs.len() as f32;
    let mut best_bias = -1.0;
    let mut best_candidate = 0;
    for (candidate, &count) in counts.iter().enumerate() {
        let bias = (count as f32 / total - 0.5).abs();
        if bias > best_bias {
            best_bias = bias;
            best_candidate = candidate;
        }
    }
    best_candidate as u8
}

// Differential Attack Implementation
// ---------------------------------

/// Compute the probability of an S-box differential
/// `delta_in`: input difference (4 bits), `delta_out`: output difference (4 bits)
/// Returns: probability = count / 16
fn diff_prob_sbox(delta_in: u8, delta_out: u8) -> f32 {
    let mut count = 0;
    for x in 0..16 {
        if SBOX[x as usize] ^ SBOX[(x ^ delta_in) as usize] == delta_out {
            count += 1;
        }
    }
    count as f32 / 16.0
}

/// Perform a differential attack to recover part of the last round key
/// `pairs`: vector of (plaintext1, plaintext2, ciphertext1, ciphertext2) tuples
/// `delta_p`: input difference for plaintexts
/// `delta_u`: expected difference before last S-box
/// `nibble_idx`: target nibble index in the last round key
/// Returns: candidate key nibble with the highest count
fn differential_attack(
    pairs: &[(u16, u16, u16, u16)],
    delta_p: u16,
    delta_u: u16,
    nibble_idx: usize,
) -> u8 {
    // Extract target nibble from expected difference
    let delta_u_nibble = (delta_u >> (4 * nibble_idx)) & 0xF;
    let mut counts = [0; 16]; // Counts for each candidate key
    
    for (p1, p2, c1, c2) in pairs {
        // Filter pairs with correct input difference
        if p1 ^ p2 != delta_p {
            continue;
        }
        
        // Target nibble in ciphertexts
        let c1_nib = (c1 >> (4 * nibble_idx)) & 0xF;
        let c2_nib = (c2 >> (4 * nibble_idx)) & 0xF;
        
        // Test each candidate key
        for candidate in 0..16 {
            // Apply candidate key and inverse S-box
            let v1 = SBOX_INV[(c1_nib ^ candidate) as usize];
            let v2 = SBOX_INV[(c2_nib ^ candidate) as usize];
            // Check output difference
            if v1 ^ v2 == delta_u_nibble as u8 {
                counts[candidate as usize] += 1;
            }
        }
    }
    
    // Find candidate with the highest count
    counts
        .iter()
        .enumerate()
        .max_by_key(|&(_, count)| count)
        .map(|(candidate, _)| candidate as u8)
        .unwrap()
}

/// Find best linear approximation for S-box
fn find_best_linear_approximation() -> (u8, u8, f32) {
    let mut best_bias = -1.0;
    let mut best_input = 0;
    let mut best_output = 0;
    
    for input_mask in 1..16u8 {
        for output_mask in 1..16u8 {
            let bias = linear_bias_sbox(input_mask, output_mask).abs();
            if bias > best_bias {
                best_bias = bias;
                best_input = input_mask;
                best_output = output_mask;
            }
        }
    }
    (best_input, best_output, best_bias)
}

/// Find best differential characteristic for S-box
fn find_best_differential() -> (u8, u8, f32) {
    let mut best_prob = -1.0;
    let mut best_input = 0;
    let mut best_output = 0;
    
    for input_diff in 1..16u8 {
        for output_diff in 0..16u8 {
            let prob = diff_prob_sbox(input_diff, output_diff);
            if prob > best_prob {
                best_prob = prob;
                best_input = input_diff;
                best_output = output_diff;
            }
        }
    }
    (best_input, best_output, best_prob)
}

// Main Function for Demonstration
// ------------------------------
fn main() {
    // Example master key (80 bits) and round key generation
    let master_key: u128 = 0x1234_5678_90AB_CDEF_1234;
    let round_keys = expand_key(master_key, 5);
    println!("Master Key: {:X}", master_key);
    println!("Round Keys: {:?}", round_keys.iter().map(|k| format!("{:04X}", k)).collect::<Vec<_>>());
    
    // Test encryption/decryption
    let plaintext: u16 = 0xABCD;
    let ciphertext = encrypt(plaintext, &round_keys);
    let decrypted = decrypt(ciphertext, &round_keys);
    println!("Plaintext:  {:04X}", plaintext);
    println!("Ciphertext: {:04X}", ciphertext);
    println!("Decrypted:  {:04X}", decrypted);
    assert_eq!(plaintext, decrypted);
    
    // Analyze S-box properties
    let (best_in_lin, best_out_lin, best_bias) = find_best_linear_approximation();
    println!("\nS-box Linear Analysis:");
    println!("Best linear approximation: input mask {:X}, output mask {:X}, bias: {:.4}", 
             best_in_lin, best_out_lin, best_bias);
    
    let (best_in_diff, best_out_diff, best_prob) = find_best_differential();
    println!("Best differential characteristic: input diff {:X}, output diff {:X}, probability: {:.4}", 
             best_in_diff, best_out_diff, best_prob);
    
    // Linear Attack Demo
    // -----------------
    // Use best linear approximation for attack
    let alpha = (best_in_lin as u16) << 4; // Apply to second nibble
    let beta = (best_out_lin as u16) << 8; // Apply to third nibble
    let nibble_idx = 2; // Target third nibble (0-3)
    
    println!("\nUsing linear approximation with bias {:.4} for attack", best_bias);
    println!("Alpha mask: {:04X}, Beta mask: {:04X}, Target nibble: {}", alpha, beta, nibble_idx);
    
    // Generate plaintext-ciphertext pairs
    let num_pairs = 10000;
    let mut pairs = Vec::new();
    for i in 0..num_pairs {
        let plain = i as u16; // Simple plaintexts
        let cipher = encrypt(plain, &round_keys);
        pairs.push((plain, cipher));
    }
    
    // Recover part of the last round key
    let recovered_nibble = linear_attack(&pairs, alpha, beta, nibble_idx);
    println!("\nLinear Attack Result:");
    println!("Recovered key nibble {}: {:X}", nibble_idx, recovered_nibble);
    
    // Extract actual last round key nibble for verification
    let actual_key_nibble = (round_keys[4] >> (4 * nibble_idx)) & 0xF;
    println!("Actual key nibble {}:    {:X}", nibble_idx, actual_key_nibble);
    
    // Differential Attack Demo
    // -----------------------
    // Use best differential characteristic for attack
    let delta_p = (best_in_diff as u16) << 4; // Apply to second nibble
    let delta_u = (best_out_diff as u16) << 4; // Apply to second nibble
    let nibble_idx = 1;   // Target second nibble
    
    println!("\nUsing differential with probability {:.4} for attack", best_prob);
    println!("Input difference: {:04X}, Expected output difference: {:04X}, Target nibble: {}", 
             delta_p, delta_u, nibble_idx);
    
    // Generate chosen plaintext pairs with fixed difference
    let num_pairs = 5000;
    let mut pairs = Vec::new();
    for i in 0..num_pairs {
        let p1 = i as u16;
        let p2 = p1 ^ delta_p;
        let c1 = encrypt(p1, &round_keys);
        let c2 = encrypt(p2, &round_keys);
        pairs.push((p1, p2, c1, c2));
    }
    
    // Recover part of the last round key
    let recovered_nibble = differential_attack(&pairs, delta_p, delta_u, nibble_idx);
    println!("\nDifferential Attack Result:");
    println!("Recovered key nibble {}: {:X}", nibble_idx, recovered_nibble);
    
    // Extract actual last round key nibble for verification
    let actual_key_nibble = (round_keys[4] >> (4 * nibble_idx)) & 0xF;
    println!("Actual key nibble {}:    {:X}", nibble_idx, actual_key_nibble);
}