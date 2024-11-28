// This file is part of Astar.

// Copyright (C) Stake Technologies Pte.Ltd.
// SPDX-License-Identifier: GPL-3.0-or-later

// Astar is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Astar is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Astar. If not, see <http://www.gnu.org/licenses/>.

use crate::test::mock::*;
use super::*;
use crate::{AccountLedger, CurrentEraInfo, EraInfo, Ledger, UnlockingChunk, Config};
use frame_support::traits::{OnRuntimeUpgrade, Get};
use frame_support::{pallet_prelude::Weight, testing_prelude::bounded_vec};
use crate::migration::LazyMigration;
use crate::weights::WeightInfo;
use sp_runtime::traits::SaturatedConversion;

// Define test weight info for our migration
struct TestWeightInfo;


impl WeightInfo for TestWeightInfo {
    fn maintenance_mode() -> Weight { Weight::zero() }
    fn register() -> Weight { Weight::zero() }
    fn set_dapp_reward_beneficiary() -> Weight { Weight::zero() }
    fn set_dapp_owner() -> Weight { Weight::zero() }
    fn unregister() -> Weight { Weight::zero() }
    fn lock_new_account() -> Weight { Weight::zero() }
    fn lock_existing_account() -> Weight { Weight::zero() }
    fn unlock() -> Weight { Weight::zero() }
    fn claim_unlocked(x: u32, ) -> Weight { Weight::zero() }  // Keep the comma after u32
    fn relock_unlocking() -> Weight { Weight::zero() }
    fn stake() -> Weight { Weight::zero() }
    fn unstake() -> Weight { Weight::zero() }
    fn claim_staker_rewards_past_period(x: u32, ) -> Weight { Weight::zero() }  // Keep the comma
    fn claim_staker_rewards_ongoing_period(x: u32, ) -> Weight { Weight::zero() }  // Keep the comma
    fn claim_bonus_reward() -> Weight { Weight::zero() }
    fn claim_dapp_reward() -> Weight { Weight::zero() }
    fn unstake_from_unregistered() -> Weight { Weight::zero() }
    fn cleanup_expired_entries(x: u32, ) -> Weight { Weight::zero() }  // Keep the comma
    fn force() -> Weight { Weight::zero() }
    fn on_initialize_voting_to_build_and_earn() -> Weight { Weight::zero() }
    fn on_initialize_build_and_earn_to_voting() -> Weight { Weight::zero() }
    fn on_initialize_build_and_earn_to_build_and_earn() -> Weight { Weight::zero() }
    fn dapp_tier_assignment(x: u32, ) -> Weight { Weight::zero() }  // Keep the comma
    fn on_idle_cleanup() -> Weight { Weight::zero() }
    fn step() -> Weight { Weight::from_parts(1, 0) }
    fn move_stake() -> Weight { Weight::zero() }
}
// The actual migration implementation
impl<T: Config, W: WeightInfo> OnRuntimeUpgrade for LazyMigration<T, W> {
    fn on_runtime_upgrade() -> Weight {
        let mut total_migrated = 0;
        let mut total_weight = Weight::zero();
        
        // Get current block number for calculations
        let current_block = frame_system::Pallet::<T>::block_number()
            .saturated_into::<u32>();

        // Translate transforms old storage to new storage
        // In this case, we're doubling the remaining unlock time for each chunk
        Ledger::<T>::translate(
            |_key: T::AccountId, mut ledger: AccountLedger<T::MaxUnlockingChunks>| {
                total_migrated += 1;

                // Process each unlocking chunk
                for chunk in ledger.unlocking.iter_mut() {
                    // Skip already unlocked chunks
                    if current_block >= chunk.unlock_block {
                        continue;
                    }

                    // Calculate remaining blocks until unlock
                    let remaining = chunk.unlock_block.saturating_sub(current_block);
                    
                    // Double the remaining time and add to current block
                    chunk.unlock_block = current_block.saturating_add(remaining.saturating_mul(2));
                }

                // Add weight for this item's migration
                total_weight = total_weight.saturating_add(W::step());
                
                // Return modified ledger
                Some(ledger)
            }
        );

        total_weight
    }
}

// Test to verify migration works correctly
#[test]
fn lazy_migrations() {
    ExtBuilder::default().build().execute_with(|| {
        // Set up initial state - block 5
        run_to_block(5);

        // Create test account with unlocking chunks
        let account = 1u64;
        let ledger = AccountLedger {
            locked: 1000,
            // Two unlocking chunks:
            // 1. At block 5 (already unlockable)
            // 2. At block 20 (should be extended)
            unlocking: bounded_vec![
                UnlockingChunk {
                    amount: 100,
                    unlock_block: 5,
                },
                UnlockingChunk {
                    amount: 100,
                    unlock_block: 20,
                },
            ],
            staked: Default::default(),
            staked_future: None,
            contract_stake_count: 0,
        };

        // Insert the test ledger
        Ledger::<Test>::insert(account, ledger.clone());

        // Run migration
        let weight = LazyMigration::<Test, TestWeightInfo>::on_runtime_upgrade();
        
        // Verify migration consumed some weight
        assert!(weight.any_gt(Weight::zero()));

        // Expected result:
        // - First chunk stays at 5 (already unlockable)
        // - Second chunk moves to 35:
        //   current_block = 5
        //   remaining = 20 - 5 = 15
        //   new_remaining = 15 * 2 = 30
        //   new_unlock = 5 + 30 = 35 
        let expected_ledger = AccountLedger {
            unlocking: bounded_vec![
                UnlockingChunk {
                    amount: 100,
                    unlock_block: 5,
                },
                UnlockingChunk {
                    amount: 100,
                    unlock_block: 35,
                },
            ],
            ..ledger
        };

        // Verify migration produced expected result
        assert_eq!(
            Ledger::<Test>::get(account),
            expected_ledger,
            "Migration should double remaining blocks"
        );
    });
}