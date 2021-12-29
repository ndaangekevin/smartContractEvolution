

// SPDX-License-Identifier: MIT
pragma solidity 0.6.12;
pragma experimental ABIEncoderV2;

/******************************************************************************\
* Author: Nick Mudge <nick@perfectabstractions.com> (https://twitter.com/mudgen)
/******************************************************************************/

library LibDiamondStorage {
    struct FacetAddressAndPosition {
        address facetAddress;
        uint16 functionSelectorPosition; // position in facetFunctionSelectors.functionSelectors array
    }

    struct FacetFunctionSelectors {
        bytes4[] functionSelectors;
        uint16 facetAddressPosition; // position of facetAddress in facetAddresses array
    }

    struct DiamondStorage {
        // maps function selector to the facet address and
        // the position of the facet address in the facetAddresses array
        // and the position of the selector in the facetSelectors.selectors array
        mapping(bytes4 => FacetAddressAndPosition) selectorToFacetAndPosition;
        // maps facet addresses to function selectors
        mapping(address => FacetFunctionSelectors) facetFunctionSelectors;
        // facet addresses
        address[] facetAddresses;
        // Used to query if a contract implements an interface.
        // Used to implement ERC-165.
        mapping(bytes4 => bool) supportedInterfaces;
    }

    bytes32 constant DIAMOND_STORAGE_POSITION = keccak256("diamond.standard.diamond.storage");

    function diamondStorage() internal pure returns (DiamondStorage storage ds) {
        bytes32 position = DIAMOND_STORAGE_POSITION;
        assembly {
            ds_slot := position
        }
    }
}

// SPDX-License-Identifier: MIT
pragma solidity 0.6.12;
pragma experimental ABIEncoderV2;

/******************************************************************************\
* Author: Nick Mudge <nick@perfectabstractions.com> (https://twitter.com/mudgen)
/******************************************************************************/

interface IDiamondCut {
    enum FacetCutAction { Add, Replace, Remove }

    struct FacetCut {
        address facetAddress;
        FacetCutAction action;
        bytes4[] functionSelectors;
    }

    event DiamondCut(FacetCut[] _diamondCut, address _init, bytes _calldata);

    /// @notice Add/replace/remove any number of functions and optionally execute
    ///         a function with delegatecall
    /// @param _diamondCut Contains the facet addresses and function selectors
    /// @param _init The address of the contract or facet to execute _calldata
    /// @param _calldata A function call, including function selector and arguments
    ///                  _calldata is executed with delegatecall on _init
    function diamondCut(
        FacetCut[] calldata _diamondCut,
        address _init,
        bytes calldata _calldata
    ) external;
}


// SPDX-License-Identifier: MIT
pragma solidity 0.6.12;
pragma experimental ABIEncoderV2;

/******************************************************************************\
* Author: Nick Mudge <nick@perfectabstractions.com> (https://twitter.com/mudgen)
/******************************************************************************/

import "./IDiamondCut.sol";

// A loupe is a small magnifying glass used to look at diamonds.
// These functions look at diamonds
interface IDiamondLoupe {
    /// These functions are expected to be called frequently
    /// by tools.

    struct Facet {
        address facetAddress;
        bytes4[] functionSelectors;
    }

    /// @notice Gets all facet addresses and their four byte function selectors.
    /// @return facets_ Facet
    function facets() external view returns (Facet[] memory facets_);

    /// @notice Gets all the function selectors supported by a specific facet.
    /// @param _facet The facet address.
    /// @return facetFunctionSelectors_
    function facetFunctionSelectors(address _facet) external view returns (bytes4[] memory facetFunctionSelectors_);

    /// @notice Get all the facet addresses used by a diamond.
    /// @return facetAddresses_
    function facetAddresses() external view returns (address[] memory facetAddresses_);

    /// @notice Gets the facet that supports the given selector.
    /// @dev If facet is not found return address(0).
    /// @param _functionSelector The function selector.
    /// @return facetAddress_ The facet address.
    function facetAddress(bytes4 _functionSelector) external view returns (address facetAddress_);
}
// SPDX-License-Identifier: MIT
pragma solidity 0.6.12;
pragma experimental ABIEncoderV2;

interface IERC165 {
    /// @notice Query if a contract implements an interface
    /// @param interfaceId The interface identifier, as specified in ERC-165
    /// @dev Interface identification is specified in ERC-165. This function
    ///  uses less than 30,000 gas.
    /// @return `true` if the contract implements `interfaceID` and
    ///  `interfaceID` is not 0xffffffff, `false` otherwise
    function supportsInterface(bytes4 interfaceId) external view returns (bool);
}


// SPDX-License-Identifier: MIT
pragma solidity 0.6.12;
pragma experimental ABIEncoderV2;

interface IDDX {
    function transfer(address _recipient, uint256 _amount) external returns (bool);

    function mint(address _recipient, uint256 _amount) external;

    function delegate(address _delegatee) external;

    function transferFrom(
        address _sender,
        address _recipient,
        uint256 _amount
    ) external returns (bool);

    function approve(address _spender, uint256 _amount) external returns (bool);

    function getPriorVotes(address account, uint256 blockNumber) external view returns (uint96);

    function totalSupply() external view returns (uint256);
}




// SPDX-License-Identifier: MIT
pragma solidity 0.6.12;
pragma experimental ABIEncoderV2;

import { IDDX } from "../tokens/interfaces/IDDX.sol";

library LibDiamondStorageDerivaDEX {
    struct DiamondStorageDerivaDEX {
        string name;
        address admin;
        IDDX ddxToken;
    }

    bytes32 constant DIAMOND_STORAGE_POSITION_DERIVADEX =
        keccak256("diamond.standard.diamond.storage.DerivaDEX.DerivaDEX");

    function diamondStorageDerivaDEX() internal pure returns (DiamondStorageDerivaDEX storage ds) {
        bytes32 position = DIAMOND_STORAGE_POSITION_DERIVADEX;
        assembly {
            ds_slot := position
        }
    }
}
// SPDX-License-Identifier: MIT

pragma solidity ^0.6.0;

/**
 * @dev Wrappers over Solidity's arithmetic operations with added overflow
 * checks.
 *
 * Arithmetic operations in Solidity wrap on overflow. This can easily result
 * in bugs, because programmers usually assume that an overflow raises an
 * error, which is the standard behavior in high level programming languages.
 * `SafeMath` restores this intuition by reverting the transaction when an
 * operation overflows.
 *
 * Using this library instead of the unchecked operations eliminates an entire
 * class of bugs, so it's recommended to use it always.
 */
library SafeMath {
    /**
     * @dev Returns the addition of two unsigned integers, reverting on
     * overflow.
     *
     * Counterpart to Solidity's `+` operator.
     *
     * Requirements:
     *
     * - Addition cannot overflow.
     */
    function add(uint256 a, uint256 b) internal pure returns (uint256) {
        uint256 c = a + b;
        require(c >= a, "SafeMath: addition overflow");

        return c;
    }

    /**
     * @dev Returns the subtraction of two unsigned integers, reverting on
     * overflow (when the result is negative).
     *
     * Counterpart to Solidity's `-` operator.
     *
     * Requirements:
     *
     * - Subtraction cannot overflow.
     */
    function sub(uint256 a, uint256 b) internal pure returns (uint256) {
        return sub(a, b, "SafeMath: subtraction overflow");
    }

    /**
     * @dev Returns the subtraction of two unsigned integers, reverting with custom message on
     * overflow (when the result is negative).
     *
     * Counterpart to Solidity's `-` operator.
     *
     * Requirements:
     *
     * - Subtraction cannot overflow.
     */
    function sub(uint256 a, uint256 b, string memory errorMessage) internal pure returns (uint256) {
        require(b <= a, errorMessage);
        uint256 c = a - b;

        return c;
    }

    /**
     * @dev Returns the multiplication of two unsigned integers, reverting on
     * overflow.
     *
     * Counterpart to Solidity's `*` operator.
     *
     * Requirements:
     *
     * - Multiplication cannot overflow.
     */
    function mul(uint256 a, uint256 b) internal pure returns (uint256) {
        // Gas optimization: this is cheaper than requiring 'a' not being zero, but the
        // benefit is lost if 'b' is also tested.
        // See: https://github.com/OpenZeppelin/openzeppelin-contracts/pull/522
        if (a == 0) {
            return 0;
        }

        uint256 c = a * b;
        require(c / a == b, "SafeMath: multiplication overflow");

        return c;
    }

    /**
     * @dev Returns the integer division of two unsigned integers. Reverts on
     * division by zero. The result is rounded towards zero.
     *
     * Counterpart to Solidity's `/` operator. Note: this function uses a
     * `revert` opcode (which leaves remaining gas untouched) while Solidity
     * uses an invalid opcode to revert (consuming all remaining gas).
     *
     * Requirements:
     *
     * - The divisor cannot be zero.
     */
    function div(uint256 a, uint256 b) internal pure returns (uint256) {
        return div(a, b, "SafeMath: division by zero");
    }

    /**
     * @dev Returns the integer division of two unsigned integers. Reverts with custom message on
     * division by zero. The result is rounded towards zero.
     *
     * Counterpart to Solidity's `/` operator. Note: this function uses a
     * `revert` opcode (which leaves remaining gas untouched) while Solidity
     * uses an invalid opcode to revert (consuming all remaining gas).
     *
     * Requirements:
     *
     * - The divisor cannot be zero.
     */
    function div(uint256 a, uint256 b, string memory errorMessage) internal pure returns (uint256) {
        require(b > 0, errorMessage);
        uint256 c = a / b;
        // assert(a == b * c + a % b); // There is no case in which this doesn't hold

        return c;
    }

    /**
     * @dev Returns the remainder of dividing two unsigned integers. (unsigned integer modulo),
     * Reverts when dividing by zero.
     *
     * Counterpart to Solidity's `%` operator. This function uses a `revert`
     * opcode (which leaves remaining gas untouched) while Solidity uses an
     * invalid opcode to revert (consuming all remaining gas).
     *
     * Requirements:
     *
     * - The divisor cannot be zero.
     */
    function mod(uint256 a, uint256 b) internal pure returns (uint256) {
        return mod(a, b, "SafeMath: modulo by zero");
    }

    /**
     * @dev Returns the remainder of dividing two unsigned integers. (unsigned integer modulo),
     * Reverts with custom message when dividing by zero.
     *
     * Counterpart to Solidity's `%` operator. This function uses a `revert`
     * opcode (which leaves remaining gas untouched) while Solidity uses an
     * invalid opcode to revert (consuming all remaining gas).
     *
     * Requirements:
     *
     * - The divisor cannot be zero.
     */
    function mod(uint256 a, uint256 b, string memory errorMessage) internal pure returns (uint256) {
        require(b != 0, errorMessage);
        return a % b;
    }
}

// SPDX-License-Identifier: MIT

pragma solidity ^0.6.0;

/**
 * @dev Interface of the ERC20 standard as defined in the EIP.
 */
interface IERC20 {
    /**
     * @dev Returns the amount of tokens in existence.
     */
    function totalSupply() external view returns (uint256);

    /**
     * @dev Returns the amount of tokens owned by `account`.
     */
    function balanceOf(address account) external view returns (uint256);

    /**
     * @dev Moves `amount` tokens from the caller's account to `recipient`.
     *
     * Returns a boolean value indicating whether the operation succeeded.
     *
     * Emits a {Transfer} event.
     */
    function transfer(address recipient, uint256 amount) external returns (bool);

    /**
     * @dev Returns the remaining number of tokens that `spender` will be
     * allowed to spend on behalf of `owner` through {transferFrom}. This is
     * zero by default.
     *
     * This value changes when {approve} or {transferFrom} are called.
     */
    function allowance(address owner, address spender) external view returns (uint256);

    /**
     * @dev Sets `amount` as the allowance of `spender` over the caller's tokens.
     *
     * Returns a boolean value indicating whether the operation succeeded.
     *
     * IMPORTANT: Beware that changing an allowance with this method brings the risk
     * that someone may use both the old and the new allowance by unfortunate
     * transaction ordering. One possible solution to mitigate this race
     * condition is to first reduce the spender's allowance to 0 and set the
     * desired value afterwards:
     * https://github.com/ethereum/EIPs/issues/20#issuecomment-263524729
     *
     * Emits an {Approval} event.
     */
    function approve(address spender, uint256 amount) external returns (bool);

    /**
     * @dev Moves `amount` tokens from `sender` to `recipient` using the
     * allowance mechanism. `amount` is then deducted from the caller's
     * allowance.
     *
     * Returns a boolean value indicating whether the operation succeeded.
     *
     * Emits a {Transfer} event.
     */
    function transferFrom(address sender, address recipient, uint256 amount) external returns (bool);

    /**
     * @dev Emitted when `value` tokens are moved from one account (`from`) to
     * another (`to`).
     *
     * Note that `value` may be zero.
     */
    event Transfer(address indexed from, address indexed to, uint256 value);

    /**
     * @dev Emitted when the allowance of a `spender` for an `owner` is set by
     * a call to {approve}. `value` is the new allowance.
     */
    event Approval(address indexed owner, address indexed spender, uint256 value);
}

// SPDX-License-Identifier: MIT
pragma solidity 0.6.12;

/**
 * @dev Wrappers over Solidity's arithmetic operations with added overflow
 * checks.
 *
 * Arithmetic operations in Solidity wrap on overflow. This can easily result
 * in bugs, because programmers usually assume that an overflow raises an
 * error, which is the standard behavior in high level programming languages.
 * `SafeMath` restores this intuition by reverting the transaction when an
 * operation overflows.
 *
 * Using this library instead of the unchecked operations eliminates an entire
 * class of bugs, so it's recommended to use it always.
 */
library SafeMath96 {
    /**
     * @dev Returns the addition of two unsigned integers, reverting on
     * overflow.
     *
     * Counterpart to Solidity's `+` operator.
     *
     * Requirements:
     *
     * - Addition cannot overflow.
     */
    function add96(uint96 a, uint96 b) internal pure returns (uint96) {
        uint96 c = a + b;
        require(c >= a, "SafeMath: addition overflow");

        return c;
    }

    /**
     * @dev Returns the subtraction of two unsigned integers, reverting on
     * overflow (when the result is negative).
     *
     * Counterpart to Solidity's `-` operator.
     *
     * Requirements:
     *
     * - Subtraction cannot overflow.
     */
    function sub96(uint96 a, uint96 b) internal pure returns (uint96) {
        return sub96(a, b, "SafeMath: subtraction overflow");
    }

    /**
     * @dev Returns the subtraction of two unsigned integers, reverting with custom message on
     * overflow (when the result is negative).
     *
     * Counterpart to Solidity's `-` operator.
     *
     * Requirements:
     *
     * - Subtraction cannot overflow.
     */
    function sub96(
        uint96 a,
        uint96 b,
        string memory errorMessage
    ) internal pure returns (uint96) {
        require(b <= a, errorMessage);
        uint96 c = a - b;

        return c;
    }
}
// SPDX-License-Identifier: MIT
pragma solidity 0.6.12;

import { IDDX } from "./IDDX.sol";

interface IDDXWalletCloneable {
    function initialize(
        address _trader,
        IDDX _ddxToken,
        address _derivaDEX
    ) external;
}

// SPDX-License-Identifier: MIT

pragma solidity ^0.6.2;

/**
 * @dev Collection of functions related to the address type
 */
library Address {
    /**
     * @dev Returns true if `account` is a contract.
     *
     * [IMPORTANT]
     * ====
     * It is unsafe to assume that an address for which this function returns
     * false is an externally-owned account (EOA) and not a contract.
     *
     * Among others, `isContract` will return false for the following
     * types of addresses:
     *
     *  - an externally-owned account
     *  - a contract in construction
     *  - an address where a contract will be created
     *  - an address where a contract lived, but was destroyed
     * ====
     */
    function isContract(address account) internal view returns (bool) {
        // This method relies in extcodesize, which returns 0 for contracts in
        // construction, since the code is only stored at the end of the
        // constructor execution.

        uint256 size;
        // solhint-disable-next-line no-inline-assembly
        assembly { size := extcodesize(account) }
        return size > 0;
    }

    /**
     * @dev Replacement for Solidity's `transfer`: sends `amount` wei to
     * `recipient`, forwarding all available gas and reverting on errors.
     *
     * https://eips.ethereum.org/EIPS/eip-1884[EIP1884] increases the gas cost
     * of certain opcodes, possibly making contracts go over the 2300 gas limit
     * imposed by `transfer`, making them unable to receive funds via
     * `transfer`. {sendValue} removes this limitation.
     *
     * https://diligence.consensys.net/posts/2019/09/stop-using-soliditys-transfer-now/[Learn more].
     *
     * IMPORTANT: because control is transferred to `recipient`, care must be
     * taken to not create reentrancy vulnerabilities. Consider using
     * {ReentrancyGuard} or the
     * https://solidity.readthedocs.io/en/v0.5.11/security-considerations.html#use-the-checks-effects-interactions-pattern[checks-effects-interactions pattern].
     */
    function sendValue(address payable recipient, uint256 amount) internal {
        require(address(this).balance >= amount, "Address: insufficient balance");

        // solhint-disable-next-line avoid-low-level-calls, avoid-call-value
        (bool success, ) = recipient.call{ value: amount }("");
        require(success, "Address: unable to send value, recipient may have reverted");
    }

    /**
     * @dev Performs a Solidity function call using a low level `call`. A
     * plain`call` is an unsafe replacement for a function call: use this
     * function instead.
     *
     * If `target` reverts with a revert reason, it is bubbled up by this
     * function (like regular Solidity function calls).
     *
     * Returns the raw returned data. To convert to the expected return value,
     * use https://solidity.readthedocs.io/en/latest/units-and-global-variables.html?highlight=abi.decode#abi-encoding-and-decoding-functions[`abi.decode`].
     *
     * Requirements:
     *
     * - `target` must be a contract.
     * - calling `target` with `data` must not revert.
     *
     * _Available since v3.1._
     */
    function functionCall(address target, bytes memory data) internal returns (bytes memory) {
      return functionCall(target, data, "Address: low-level call failed");
    }

    /**
     * @dev Same as {xref-Address-functionCall-address-bytes-}[`functionCall`], but with
     * `errorMessage` as a fallback revert reason when `target` reverts.
     *
     * _Available since v3.1._
     */
    function functionCall(address target, bytes memory data, string memory errorMessage) internal returns (bytes memory) {
        return _functionCallWithValue(target, data, 0, errorMessage);
    }

    /**
     * @dev Same as {xref-Address-functionCall-address-bytes-}[`functionCall`],
     * but also transferring `value` wei to `target`.
     *
     * Requirements:
     *
     * - the calling contract must have an ETH balance of at least `value`.
     * - the called Solidity function must be `payable`.
     *
     * _Available since v3.1._
     */
    function functionCallWithValue(address target, bytes memory data, uint256 value) internal returns (bytes memory) {
        return functionCallWithValue(target, data, value, "Address: low-level call with value failed");
    }

    /**
     * @dev Same as {xref-Address-functionCallWithValue-address-bytes-uint256-}[`functionCallWithValue`], but
     * with `errorMessage` as a fallback revert reason when `target` reverts.
     *
     * _Available since v3.1._
     */
    function functionCallWithValue(address target, bytes memory data, uint256 value, string memory errorMessage) internal returns (bytes memory) {
        require(address(this).balance >= value, "Address: insufficient balance for call");
        return _functionCallWithValue(target, data, value, errorMessage);
    }

    function _functionCallWithValue(address target, bytes memory data, uint256 weiValue, string memory errorMessage) private returns (bytes memory) {
        require(isContract(target), "Address: call to non-contract");

        // solhint-disable-next-line avoid-low-level-calls
        (bool success, bytes memory returndata) = target.call{ value: weiValue }(data);
        if (success) {
            return returndata;
        } else {
            // Look for revert reason and bubble it up if present
            if (returndata.length > 0) {
                // The easiest way to bubble the revert reason is using memory via assembly

                // solhint-disable-next-line no-inline-assembly
                assembly {
                    let returndata_size := mload(returndata)
                    revert(add(32, returndata), returndata_size)
                }
            } else {
                revert(errorMessage);
            }
        }
    }
}

// SPDX-License-Identifier: MIT
pragma solidity 0.6.12;

/*
    The MIT License (MIT)
    Copyright (c) 2018 Murray Software, LLC.
    Permission is hereby granted, free of charge, to any person obtaining
    a copy of this software and associated documentation files (the
    "Software"), to deal in the Software without restriction, including
    without limitation the rights to use, copy, modify, merge, publish,
    distribute, sublicense, and/or sell copies of the Software, and to
    permit persons to whom the Software is furnished to do so, subject to
    the following conditions:
    The above copyright notice and this permission notice shall be included
    in all copies or substantial portions of the Software.
    THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS
    OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
    MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT.
    IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY
    CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT,
    TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION WITH THE
    SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
*/
//solhint-disable max-line-length
//solhint-disable no-inline-assembly

library LibClone {
    function createClone(address target) internal returns (address result) {
        bytes20 targetBytes = bytes20(target);
        assembly {
            let clone := mload(0x40)
            mstore(clone, 0x3d602d80600a3d3981f3363d3d373d3d3d363d73000000000000000000000000)
            mstore(add(clone, 0x14), targetBytes)
            mstore(add(clone, 0x28), 0x5af43d82803e903d91602b57fd5bf30000000000000000000000000000000000)
            result := create(0, clone, 0x37)
        }
    }

    function isClone(address target, address query) internal view returns (bool result) {
        bytes20 targetBytes = bytes20(target);
        assembly {
            let clone := mload(0x40)
            mstore(clone, 0x363d3d373d3d3d363d7300000000000000000000000000000000000000000000)
            mstore(add(clone, 0xa), targetBytes)
            mstore(add(clone, 0x1e), 0x5af43d82803e903d91602b57fd5bf30000000000000000000000000000000000)

            let other := add(clone, 0x40)
            extcodecopy(query, other, 0, 0x2d)
            result := and(eq(mload(clone), mload(other)), eq(mload(add(clone, 0xd)), mload(add(other, 0xd))))
        }
    }
}

// SPDX-License-Identifier: MIT

pragma solidity ^0.6.0;

/**
 * @dev Standard math utilities missing in the Solidity language.
 */
library Math {
    /**
     * @dev Returns the largest of two numbers.
     */
    function max(uint256 a, uint256 b) internal pure returns (uint256) {
        return a >= b ? a : b;
    }

    /**
     * @dev Returns the smallest of two numbers.
     */
    function min(uint256 a, uint256 b) internal pure returns (uint256) {
        return a < b ? a : b;
    }

    /**
     * @dev Returns the average of two numbers. The result is rounded towards
     * zero.
     */
    function average(uint256 a, uint256 b) internal pure returns (uint256) {
        // (a + b) / 2 can overflow, so we distribute
        return (a / 2) + (b / 2) + ((a % 2 + b % 2) / 2);
    }
}

// SPDX-License-Identifier: MIT
pragma solidity 0.6.12;

/**
 * @dev Wrappers over Solidity's arithmetic operations with added overflow
 * checks.
 *
 * Arithmetic operations in Solidity wrap on overflow. This can easily result
 * in bugs, because programmers usually assume that an overflow raises an
 * error, which is the standard behavior in high level programming languages.
 * `SafeMath` restores this intuition by reverting the transaction when an
 * operation overflows.
 *
 * Using this library instead of the unchecked operations eliminates an entire
 * class of bugs, so it's recommended to use it always.
 */
library SafeMath32 {
    /**
     * @dev Returns the addition of two unsigned integers, reverting on
     * overflow.
     *
     * Counterpart to Solidity's `+` operator.
     *
     * Requirements:
     *
     * - Addition cannot overflow.
     */
    function add32(uint32 a, uint32 b) internal pure returns (uint32) {
        uint32 c = a + b;
        require(c >= a, "SafeMath: addition overflow");

        return c;
    }

    /**
     * @dev Returns the subtraction of two unsigned integers, reverting on
     * overflow (when the result is negative).
     *
     * Counterpart to Solidity's `-` operator.
     *
     * Requirements:
     *
     * - Subtraction cannot overflow.
     */
    function sub32(uint32 a, uint32 b) internal pure returns (uint32) {
        return sub32(a, b, "SafeMath: subtraction overflow");
    }

    /**
     * @dev Returns the subtraction of two unsigned integers, reverting with custom message on
     * overflow (when the result is negative).
     *
     * Counterpart to Solidity's `-` operator.
     *
     * Requirements:
     *
     * - Subtraction cannot overflow.
     */
    function sub32(
        uint32 a,
        uint32 b,
        string memory errorMessage
    ) internal pure returns (uint32) {
        require(b <= a, errorMessage);
        uint32 c = a - b;

        return c;
    }
}



// SPDX-License-Identifier: MIT
pragma solidity 0.6.12;

import { SafeMath } from "openzeppelin-solidity/contracts/math/SafeMath.sol";
import { Math } from "openzeppelin-solidity/contracts/math/Math.sol";
import { SafeMath96 } from "./SafeMath96.sol";

/**
 * @dev Wrappers over Solidity's arithmetic operations with added overflow
 * checks.
 *
 * Arithmetic operations in Solidity wrap on overflow. This can easily result
 * in bugs, because programmers usually assume that an overflow raises an
 * error, which is the standard behavior in high level programming languages.
 * `SafeMath` restores this intuition by reverting the transaction when an
 * operation overflows.
 *
 * Using this library instead of the unchecked operations eliminates an entire
 * class of bugs, so it's recommended to use it always.
 */
library MathHelpers {
    using SafeMath96 for uint96;
    using SafeMath for uint256;

    function proportion96(
        uint96 a,
        uint256 b,
        uint256 c
    ) internal pure returns (uint96) {
        return safe96(uint256(a).mul(b).div(c), "Amount exceeds 96 bits");
    }

    function safe96(uint256 n, string memory errorMessage) internal pure returns (uint96) {
        require(n < 2**96, errorMessage);
        return uint96(n);
    }

    function safe32(uint256 n, string memory errorMessage) internal pure returns (uint32) {
        require(n < 2**32, errorMessage);
        return uint32(n);
    }

    function safe224(uint256 n, string memory errorMessage) internal pure returns (uint224) {
        require(n < 2**224, errorMessage);
        return uint224(n);
    }

    /**
     * @dev Returns the largest of two numbers.
     */
    function clamp96(
        uint96 a,
        uint256 b,
        uint256 c
    ) internal pure returns (uint96) {
        return safe96(Math.min(Math.max(a, b), c), "Amount exceeds 96 bits");
    }

    /**
     * @dev Returns the smallest of two numbers.
     */
    function min(uint256 a, uint256 b) internal pure returns (uint256) {
        return a < b ? a : b;
    }
}
// SPDX-License-Identifier: MIT
pragma solidity 0.6.12;

interface IAToken {
    function decimals() external returns (uint256);

    function transfer(address _recipient, uint256 _amount) external;

    function balanceOf(address _user) external view returns (uint256);
}

// SPDX-License-Identifier: MIT
pragma solidity 0.6.12;

abstract contract IComptroller {
    struct CompMarketState {
        uint224 index;
        uint32 block;
    }

    /// @notice Indicator that this is a Comptroller contract (for inspection)
    bool public constant isComptroller = true; // solhint-disable-line const-name-snakecase

    // @notice The COMP market supply state for each market
    mapping(address => CompMarketState) public compSupplyState;

    /// @notice The COMP borrow index for each market for each supplier as of the last time they accrued COMP
    mapping(address => mapping(address => uint256)) public compSupplierIndex;

    /// @notice The portion of compRate that each market currently receives
    mapping(address => uint256) public compSpeeds;

    /// @notice The COMP accrued but not yet transferred to each user
    mapping(address => uint256) public compAccrued;

    /*** Assets You Are In ***/

    function enterMarkets(address[] calldata cTokens) external virtual returns (uint256[] memory);

    function exitMarket(address cToken) external virtual returns (uint256);

    /*** Policy Hooks ***/

    function mintAllowed(
        address cToken,
        address minter,
        uint256 mintAmount
    ) external virtual returns (uint256);

    function mintVerify(
        address cToken,
        address minter,
        uint256 mintAmount,
        uint256 mintTokens
    ) external virtual;

    function redeemAllowed(
        address cToken,
        address redeemer,
        uint256 redeemTokens
    ) external virtual returns (uint256);

    function redeemVerify(
        address cToken,
        address redeemer,
        uint256 redeemAmount,
        uint256 redeemTokens
    ) external virtual;

    function borrowAllowed(
        address cToken,
        address borrower,
        uint256 borrowAmount
    ) external virtual returns (uint256);

    function borrowVerify(
        address cToken,
        address borrower,
        uint256 borrowAmount
    ) external virtual;

    function repayBorrowAllowed(
        address cToken,
        address payer,
        address borrower,
        uint256 repayAmount
    ) external virtual returns (uint256);

    function repayBorrowVerify(
        address cToken,
        address payer,
        address borrower,
        uint256 repayAmount,
        uint256 borrowerIndex
    ) external virtual;

    function liquidateBorrowAllowed(
        address cTokenBorrowed,
        address cTokenCollateral,
        address liquidator,
        address borrower,
        uint256 repayAmount
    ) external virtual returns (uint256);

    function liquidateBorrowVerify(
        address cTokenBorrowed,
        address cTokenCollateral,
        address liquidator,
        address borrower,
        uint256 repayAmount,
        uint256 seizeTokens
    ) external virtual;

    function seizeAllowed(
        address cTokenCollateral,
        address cTokenBorrowed,
        address liquidator,
        address borrower,
        uint256 seizeTokens
    ) external virtual returns (uint256);

    function seizeVerify(
        address cTokenCollateral,
        address cTokenBorrowed,
        address liquidator,
        address borrower,
        uint256 seizeTokens
    ) external virtual;

    function transferAllowed(
        address cToken,
        address src,
        address dst,
        uint256 transferTokens
    ) external virtual returns (uint256);

    function transferVerify(
        address cToken,
        address src,
        address dst,
        uint256 transferTokens
    ) external virtual;

    /*** Liquidity/Liquidation Calculations ***/

    function liquidateCalculateSeizeTokens(
        address cTokenBorrowed,
        address cTokenCollateral,
        uint256 repayAmount
    ) external virtual returns (uint256, uint256);

    function claimComp(address holder) public virtual;
}

// SPDX-License-Identifier: MIT
pragma solidity 0.6.12;

interface ICToken {
    function accrueInterest() external returns (uint256);

    function approve(address spender, uint256 amount) external returns (bool);

    function balanceOfUnderlying(address owner) external returns (uint256);

    function borrowBalanceCurrent(address account) external returns (uint256);

    function exchangeRateCurrent() external returns (uint256);

    function seize(
        address liquidator,
        address borrower,
        uint256 seizeTokens
    ) external returns (uint256);

    function totalBorrowsCurrent() external returns (uint256);

    function transfer(address dst, uint256 amount) external returns (bool);

    function transferFrom(
        address src,
        address dst,
        uint256 amount
    ) external returns (bool);

    function allowance(address owner, address spender) external view returns (uint256);

    function balanceOf(address owner) external view returns (uint256);

    function borrowBalanceStored(address account) external view returns (uint256);

    function borrowRatePerBlock() external view returns (uint256);

    function decimals() external view returns (uint256);

    function exchangeRateStored() external view returns (uint256);

    function getAccountSnapshot(address account)
        external
        view
        returns (
            uint256,
            uint256,
            uint256,
            uint256
        );

    function getCash() external view returns (uint256);

    function supplyRatePerBlock() external view returns (uint256);
}
// SPDX-License-Identifier: MIT
pragma solidity 0.6.12;
pragma experimental ABIEncoderV2;

/**
 * @title IDIFundToken
 * @author DerivaDEX (Borrowed/inspired from Compound)
 * @notice This is the native token contract for DerivaDEX. It
 *         implements the ERC-20 standard, with additional
 *         functionality to efficiently handle the governance aspect of
 *         the DerivaDEX ecosystem.
 * @dev The contract makes use of some nonstandard types not seen in
 *      the ERC-20 standard. The DDX token makes frequent use of the
 *      uint96 data type, as opposed to the more standard uint256 type.
 *      Given the maintenance of arrays of balances, allowances, and
 *      voting checkpoints, this allows us to more efficiently pack
 *      data together, thereby resulting in cheaper transactions.
 */
interface IDIFundToken {
    function transfer(address _recipient, uint256 _amount) external returns (bool);

    function mint(address _recipient, uint256 _amount) external;

    function burnFrom(address _account, uint256 _amount) external;

    function delegate(address _delegatee) external;

    function transferFrom(
        address _sender,
        address _recipient,
        uint256 _amount
    ) external returns (bool);

    function approve(address _spender, uint256 _amount) external returns (bool);

    function getPriorValues(address account, uint256 blockNumber) external view returns (uint96);

    function getTotalPriorValues(uint256 blockNumber) external view returns (uint96);

    function balanceOf(address _account) external view returns (uint256);

    function totalSupply() external view returns (uint256);
}

// SPDX-License-Identifier: MIT
/*

  Copyright 2018 ZeroEx Intl.

  Licensed under the Apache License, Version 2.0 (the "License");
  you may not use this file except in compliance with the License.
  You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

  Unless required by applicable law or agreed to in writing, software
  distributed under the License is distributed on an "AS IS" BASIS,
  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
  See the License for the specific language governing permissions and
  limitations under the License.

*/

pragma solidity 0.6.12;

library LibBytes {
    using LibBytes for bytes;

    /// @dev Gets the memory address for a byte array.
    /// @param input Byte array to lookup.
    /// @return memoryAddress Memory address of byte array. This
    ///         points to the header of the byte array which contains
    ///         the length.
    function rawAddress(bytes memory input) internal pure returns (uint256 memoryAddress) {
        assembly {
            memoryAddress := input
        }
        return memoryAddress;
    }

    /// @dev Gets the memory address for the contents of a byte array.
    /// @param input Byte array to lookup.
    /// @return memoryAddress Memory address of the contents of the byte array.
    function contentAddress(bytes memory input) internal pure returns (uint256 memoryAddress) {
        assembly {
            memoryAddress := add(input, 32)
        }
        return memoryAddress;
    }

    /// @dev Copies `length` bytes from memory location `source` to `dest`.
    /// @param dest memory address to copy bytes to.
    /// @param source memory address to copy bytes from.
    /// @param length number of bytes to copy.
    function memCopy(
        uint256 dest,
        uint256 source,
        uint256 length
    ) internal pure {
        if (length < 32) {
            // Handle a partial word by reading destination and masking
            // off the bits we are interested in.
            // This correctly handles overlap, zero lengths and source == dest
            assembly {
                let mask := sub(exp(256, sub(32, length)), 1)
                let s := and(mload(source), not(mask))
                let d := and(mload(dest), mask)
                mstore(dest, or(s, d))
            }
        } else {
            // Skip the O(length) loop when source == dest.
            if (source == dest) {
                return;
            }

            // For large copies we copy whole words at a time. The final
            // word is aligned to the end of the range (instead of after the
            // previous) to handle partial words. So a copy will look like this:
            //
            //  ####
            //      ####
            //          ####
            //            ####
            //
            // We handle overlap in the source and destination range by
            // changing the copying direction. This prevents us from
            // overwriting parts of source that we still need to copy.
            //
            // This correctly handles source == dest
            //
            if (source > dest) {
                assembly {
                    // We subtract 32 from `sEnd` and `dEnd` because it
                    // is easier to compare with in the loop, and these
                    // are also the addresses we need for copying the
                    // last bytes.
                    length := sub(length, 32)
                    let sEnd := add(source, length)
                    let dEnd := add(dest, length)

                    // Remember the last 32 bytes of source
                    // This needs to be done here and not after the loop
                    // because we may have overwritten the last bytes in
                    // source already due to overlap.
                    let last := mload(sEnd)

                    // Copy whole words front to back
                    // Note: the first check is always true,
                    // this could have been a do-while loop.
                    // solhint-disable-next-line no-empty-blocks
                    for {

                    } lt(source, sEnd) {

                    } {
                        mstore(dest, mload(source))
                        source := add(source, 32)
                        dest := add(dest, 32)
                    }

                    // Write the last 32 bytes
                    mstore(dEnd, last)
                }
            } else {
                assembly {
                    // We subtract 32 from `sEnd` and `dEnd` because those
                    // are the starting points when copying a word at the end.
                    length := sub(length, 32)
                    let sEnd := add(source, length)
                    let dEnd := add(dest, length)

                    // Remember the first 32 bytes of source
                    // This needs to be done here and not after the loop
                    // because we may have overwritten the first bytes in
                    // source already due to overlap.
                    let first := mload(source)

                    // Copy whole words back to front
                    // We use a signed comparisson here to allow dEnd to become
                    // negative (happens when source and dest < 32). Valid
                    // addresses in local memory will never be larger than
                    // 2**255, so they can be safely re-interpreted as signed.
                    // Note: the first check is always true,
                    // this could have been a do-while loop.
                    // solhint-disable-next-line no-empty-blocks
                    for {

                    } slt(dest, dEnd) {

                    } {
                        mstore(dEnd, mload(sEnd))
                        sEnd := sub(sEnd, 32)
                        dEnd := sub(dEnd, 32)
                    }

                    // Write the first 32 bytes
                    mstore(dest, first)
                }
            }
        }
    }

    /// @dev Returns a slices from a byte array.
    /// @param b The byte array to take a slice from.
    /// @param from The starting index for the slice (inclusive).
    /// @param to The final index for the slice (exclusive).
    /// @return result The slice containing bytes at indices [from, to)
    function slice(
        bytes memory b,
        uint256 from,
        uint256 to
    ) internal pure returns (bytes memory result) {
        require(from <= to, "FROM_LESS_THAN_TO_REQUIRED");
        require(to <= b.length, "TO_LESS_THAN_LENGTH_REQUIRED");

        // Create a new bytes structure and copy contents
        result = new bytes(to - from);
        memCopy(result.contentAddress(), b.contentAddress() + from, result.length);
        return result;
    }

    /// @dev Returns a slice from a byte array without preserving the input.
    /// @param b The byte array to take a slice from. Will be destroyed in the process.
    /// @param from The starting index for the slice (inclusive).
    /// @param to The final index for the slice (exclusive).
    /// @return result The slice containing bytes at indices [from, to)
    /// @dev When `from == 0`, the original array will match the slice. In other cases its state will be corrupted.
    function sliceDestructive(
        bytes memory b,
        uint256 from,
        uint256 to
    ) internal pure returns (bytes memory result) {
        require(from <= to, "FROM_LESS_THAN_TO_REQUIRED");
        require(to <= b.length, "TO_LESS_THAN_LENGTH_REQUIRED");

        // Create a new bytes structure around [from, to) in-place.
        assembly {
            result := add(b, from)
            mstore(result, sub(to, from))
        }
        return result;
    }

    /// @dev Pops the last byte off of a byte array by modifying its length.
    /// @param b Byte array that will be modified.
    /// @return result The byte that was popped off.
    function popLastByte(bytes memory b) internal pure returns (bytes1 result) {
        require(b.length > 0, "GREATER_THAN_ZERO_LENGTH_REQUIRED");

        // Store last byte.
        result = b[b.length - 1];

        assembly {
            // Decrement length of byte array.
            let newLen := sub(mload(b), 1)
            mstore(b, newLen)
        }
        return result;
    }

    /// @dev Pops the last 20 bytes off of a byte array by modifying its length.
    /// @param b Byte array that will be modified.
    /// @return result The 20 byte address that was popped off.
    function popLast20Bytes(bytes memory b) internal pure returns (address result) {
        require(b.length >= 20, "GREATER_OR_EQUAL_TO_20_LENGTH_REQUIRED");

        // Store last 20 bytes.
        result = readAddress(b, b.length - 20);

        assembly {
            // Subtract 20 from byte array length.
            let newLen := sub(mload(b), 20)
            mstore(b, newLen)
        }
        return result;
    }

    /// @dev Tests equality of two byte arrays.
    /// @param lhs First byte array to compare.
    /// @param rhs Second byte array to compare.
    /// @return equal True if arrays are the same. False otherwise.
    function equals(bytes memory lhs, bytes memory rhs) internal pure returns (bool equal) {
        // Keccak gas cost is 30 + numWords * 6. This is a cheap way to compare.
        // We early exit on unequal lengths, but keccak would also correctly
        // handle this.
        return lhs.length == rhs.length && keccak256(lhs) == keccak256(rhs);
    }

    /// @dev Reads an address from a position in a byte array.
    /// @param b Byte array containing an address.
    /// @param index Index in byte array of address.
    /// @return result address from byte array.
    function readAddress(bytes memory b, uint256 index) internal pure returns (address result) {
        require(
            b.length >= index + 20, // 20 is length of address
            "GREATER_OR_EQUAL_TO_20_LENGTH_REQUIRED"
        );

        // Add offset to index:
        // 1. Arrays are prefixed by 32-byte length parameter (add 32 to index)
        // 2. Account for size difference between address length and 32-byte storage word (subtract 12 from index)
        index += 20;

        // Read address from array memory
        assembly {
            // 1. Add index to address of bytes array
            // 2. Load 32-byte word from memory
            // 3. Apply 20-byte mask to obtain address
            result := and(mload(add(b, index)), 0xffffffffffffffffffffffffffffffffffffffff)
        }
        return result;
    }

    /// @dev Writes an address into a specific position in a byte array.
    /// @param b Byte array to insert address into.
    /// @param index Index in byte array of address.
    /// @param input Address to put into byte array.
    function writeAddress(
        bytes memory b,
        uint256 index,
        address input
    ) internal pure {
        require(
            b.length >= index + 20, // 20 is length of address
            "GREATER_OR_EQUAL_TO_20_LENGTH_REQUIRED"
        );

        // Add offset to index:
        // 1. Arrays are prefixed by 32-byte length parameter (add 32 to index)
        // 2. Account for size difference between address length and 32-byte storage word (subtract 12 from index)
        index += 20;

        // Store address into array memory
        assembly {
            // The address occupies 20 bytes and mstore stores 32 bytes.
            // First fetch the 32-byte word where we'll be storing the address, then
            // apply a mask so we have only the bytes in the word that the address will not occupy.
            // Then combine these bytes with the address and store the 32 bytes back to memory with mstore.

            // 1. Add index to address of bytes array
            // 2. Load 32-byte word from memory
            // 3. Apply 12-byte mask to obtain extra bytes occupying word of memory where we'll store the address
            let neighbors := and(
                mload(add(b, index)),
                0xffffffffffffffffffffffff0000000000000000000000000000000000000000
            )

            // Make sure input address is clean.
            // (Solidity does not guarantee this)
            input := and(input, 0xffffffffffffffffffffffffffffffffffffffff)

            // Store the neighbors and address into memory
            mstore(add(b, index), xor(input, neighbors))
        }
    }

    /// @dev Reads a bytes32 value from a position in a byte array.
    /// @param b Byte array containing a bytes32 value.
    /// @param index Index in byte array of bytes32 value.
    /// @return result bytes32 value from byte array.
    function readBytes32(bytes memory b, uint256 index) internal pure returns (bytes32 result) {
        require(b.length >= index + 32, "GREATER_OR_EQUAL_TO_32_LENGTH_REQUIRED");

        // Arrays are prefixed by a 256 bit length parameter
        index += 32;

        // Read the bytes32 from array memory
        assembly {
            result := mload(add(b, index))
        }
        return result;
    }

    /// @dev Writes a bytes32 into a specific position in a byte array.
    /// @param b Byte array to insert <input> into.
    /// @param index Index in byte array of <input>.
    /// @param input bytes32 to put into byte array.
    function writeBytes32(
        bytes memory b,
        uint256 index,
        bytes32 input
    ) internal pure {
        require(b.length >= index + 32, "GREATER_OR_EQUAL_TO_32_LENGTH_REQUIRED");

        // Arrays are prefixed by a 256 bit length parameter
        index += 32;

        // Read the bytes32 from array memory
        assembly {
            mstore(add(b, index), input)
        }
    }

    /// @dev Reads a uint256 value from a position in a byte array.
    /// @param b Byte array containing a uint256 value.
    /// @param index Index in byte array of uint256 value.
    /// @return result uint256 value from byte array.
    function readUint256(bytes memory b, uint256 index) internal pure returns (uint256 result) {
        result = uint256(readBytes32(b, index));
        return result;
    }

    /// @dev Writes a uint256 into a specific position in a byte array.
    /// @param b Byte array to insert <input> into.
    /// @param index Index in byte array of <input>.
    /// @param input uint256 to put into byte array.
    function writeUint256(
        bytes memory b,
        uint256 index,
        uint256 input
    ) internal pure {
        writeBytes32(b, index, bytes32(input));
    }

    /// @dev Reads an unpadded bytes4 value from a position in a byte array.
    /// @param b Byte array containing a bytes4 value.
    /// @param index Index in byte array of bytes4 value.
    /// @return result bytes4 value from byte array.
    function readBytes4(bytes memory b, uint256 index) internal pure returns (bytes4 result) {
        require(b.length >= index + 4, "GREATER_OR_EQUAL_TO_4_LENGTH_REQUIRED");

        // Arrays are prefixed by a 32 byte length field
        index += 32;

        // Read the bytes4 from array memory
        assembly {
            result := mload(add(b, index))
            // Solidity does not require us to clean the trailing bytes.
            // We do it anyway
            result := and(result, 0xFFFFFFFF00000000000000000000000000000000000000000000000000000000)
        }
        return result;
    }

    /// @dev Reads nested bytes from a specific position.
    /// @dev NOTE: the returned value overlaps with the input value.
    ///            Both should be treated as immutable.
    /// @param b Byte array containing nested bytes.
    /// @param index Index of nested bytes.
    /// @return result Nested bytes.
    function readBytesWithLength(bytes memory b, uint256 index) internal pure returns (bytes memory result) {
        // Read length of nested bytes
        uint256 nestedBytesLength = readUint256(b, index);
        index += 32;

        // Assert length of <b> is valid, given
        // length of nested bytes
        require(b.length >= index + nestedBytesLength, "GREATER_OR_EQUAL_TO_NESTED_BYTES_LENGTH_REQUIRED");

        // Return a pointer to the byte array as it exists inside `b`
        assembly {
            result := add(b, index)
        }
        return result;
    }

    /// @dev Inserts bytes at a specific position in a byte array.
    /// @param b Byte array to insert <input> into.
    /// @param index Index in byte array of <input>.
    /// @param input bytes to insert.
    function writeBytesWithLength(
        bytes memory b,
        uint256 index,
        bytes memory input
    ) internal pure {
        // Assert length of <b> is valid, given
        // length of input
        require(
            b.length >= index + 32 + input.length, // 32 bytes to store length
            "GREATER_OR_EQUAL_TO_NESTED_BYTES_LENGTH_REQUIRED"
        );

        // Copy <input> into <b>
        memCopy(
            b.contentAddress() + index,
            input.rawAddress(), // includes length of <input>
            input.length + 32 // +32 bytes to store <input> length
        );
    }

    /// @dev Performs a deep copy of a byte array onto another byte array of greater than or equal length.
    /// @param dest Byte array that will be overwritten with source bytes.
    /// @param source Byte array to copy onto dest bytes.
    function deepCopyBytes(bytes memory dest, bytes memory source) internal pure {
        uint256 sourceLen = source.length;
        // Dest length must be >= source length, or some bytes would not be copied.
        require(dest.length >= sourceLen, "GREATER_OR_EQUAL_TO_SOURCE_BYTES_LENGTH_REQUIRED");
        memCopy(dest.contentAddress(), source.contentAddress(), sourceLen);
    }
}
// SPDX-License-Identifier: MIT
/*

  Copyright 2019 ZeroEx Intl.

  Licensed under the Apache License, Version 2.0 (the "License");
  you may not use this file except in compliance with the License.
  You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

  Unless required by applicable law or agreed to in writing, software
  distributed under the License is distributed on an "AS IS" BASIS,
  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
  See the License for the specific language governing permissions and
  limitations under the License.

*/

pragma solidity 0.6.12;

library LibEIP712 {
    // Hash of the EIP712 Domain Separator Schema
    // keccak256(abi.encodePacked(
    //     "EIP712Domain(",
    //     "string name,",
    //     "string version,",
    //     "uint256 chainId,",
    //     "address verifyingContract",
    //     ")"
    // ))
    bytes32 internal constant _EIP712_DOMAIN_SEPARATOR_SCHEMA_HASH =
        0x8b73c3c69bb8fe3d512ecc4cf759cc79239f7b179b0ffacaa9a75d522b39400f;

    /// @dev Calculates a EIP712 domain separator.
    /// @param name The EIP712 domain name.
    /// @param version The EIP712 domain version.
    /// @param verifyingContract The EIP712 verifying contract.
    /// @return result EIP712 domain separator.
    function hashEIP712Domain(
        string memory name,
        string memory version,
        uint256 chainId,
        address verifyingContract
    ) internal pure returns (bytes32 result) {
        bytes32 schemaHash = _EIP712_DOMAIN_SEPARATOR_SCHEMA_HASH;

        // Assembly for more efficient computing:
        // keccak256(abi.encodePacked(
        //     _EIP712_DOMAIN_SEPARATOR_SCHEMA_HASH,
        //     keccak256(bytes(name)),
        //     keccak256(bytes(version)),
        //     chainId,
        //     uint256(verifyingContract)
        // ))

        assembly {
            // Calculate hashes of dynamic data
            let nameHash := keccak256(add(name, 32), mload(name))
            let versionHash := keccak256(add(version, 32), mload(version))

            // Load free memory pointer
            let memPtr := mload(64)

            // Store params in memory
            mstore(memPtr, schemaHash)
            mstore(add(memPtr, 32), nameHash)
            mstore(add(memPtr, 64), versionHash)
            mstore(add(memPtr, 96), chainId)
            mstore(add(memPtr, 128), verifyingContract)

            // Compute hash
            result := keccak256(memPtr, 160)
        }
        return result;
    }

    /// @dev Calculates EIP712 encoding for a hash struct with a given domain hash.
    /// @param eip712DomainHash Hash of the domain domain separator data, computed
    ///                         with getDomainHash().
    /// @param hashStruct The EIP712 hash struct.
    /// @return result EIP712 hash applied to the given EIP712 Domain.
    function hashEIP712Message(bytes32 eip712DomainHash, bytes32 hashStruct) internal pure returns (bytes32 result) {
        // Assembly for more efficient computing:
        // keccak256(abi.encodePacked(
        //     EIP191_HEADER,
        //     EIP712_DOMAIN_HASH,
        //     hashStruct
        // ));

        assembly {
            // Load free memory pointer
            let memPtr := mload(64)

            mstore(memPtr, 0x1901000000000000000000000000000000000000000000000000000000000000) // EIP191 header
            mstore(add(memPtr, 2), eip712DomainHash) // EIP712 domain hash
            mstore(add(memPtr, 34), hashStruct) // Hash of struct

            // Compute hash
            result := keccak256(memPtr, 66)
        }
        return result;
    }
}

// SPDX-License-Identifier: MIT
/*

  Copyright 2018 ZeroEx Intl.

  Licensed under the Apache License, Version 2.0 (the "License");
  you may not use this file except in compliance with the License.
  You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

  Unless required by applicable law or agreed to in writing, software
  distributed under the License is distributed on an "AS IS" BASIS,
  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
  See the License for the specific language governing permissions and
  limitations under the License.

*/

pragma solidity 0.6.12;

import { LibEIP712 } from "./LibEIP712.sol";

library LibPermit {
    struct Permit {
        address spender; // Spender
        uint256 value; // Value
        uint256 nonce; // Nonce
        uint256 expiry; // Expiry
    }

    // Hash for the EIP712 LibPermit Schema
    //    bytes32 constant internal EIP712_PERMIT_SCHEMA_HASH = keccak256(abi.encodePacked(
    //        "Permit(",
    //        "address spender,",
    //        "uint256 value,",
    //        "uint256 nonce,",
    //        "uint256 expiry",
    //        ")"
    //    ));
    bytes32 internal constant EIP712_PERMIT_SCHEMA_HASH =
        0x58e19c95adc541dea238d3211d11e11e7def7d0c7fda4e10e0c45eb224ef2fb7;

    /// @dev Calculates Keccak-256 hash of the permit.
    /// @param permit The permit structure.
    /// @return permitHash Keccak-256 EIP712 hash of the permit.
    function getPermitHash(Permit memory permit, bytes32 eip712ExchangeDomainHash)
        internal
        pure
        returns (bytes32 permitHash)
    {
        permitHash = LibEIP712.hashEIP712Message(eip712ExchangeDomainHash, hashPermit(permit));
        return permitHash;
    }

    /// @dev Calculates EIP712 hash of the permit.
    /// @param permit The permit structure.
    /// @return result EIP712 hash of the permit.
    function hashPermit(Permit memory permit) internal pure returns (bytes32 result) {
        // Assembly for more efficiently computing:
        bytes32 schemaHash = EIP712_PERMIT_SCHEMA_HASH;

        assembly {
            // Assert permit offset (this is an internal error that should never be triggered)
            if lt(permit, 32) {
                invalid()
            }

            // Calculate memory addresses that will be swapped out before hashing
            let pos1 := sub(permit, 32)

            // Backup
            let temp1 := mload(pos1)

            // Hash in place
            mstore(pos1, schemaHash)
            result := keccak256(pos1, 160)

            // Restore
            mstore(pos1, temp1)
        }
        return result;
    }
}
// SPDX-License-Identifier: MIT
pragma solidity 0.6.12;

interface IInsuranceFund {
    function claimDDXFromInsuranceMining(address _claimant) external;
}


// SPDX-License-Identifier: MIT
/*

  Copyright 2018 ZeroEx Intl.

  Licensed under the Apache License, Version 2.0 (the "License");
  you may not use this file except in compliance with the License.
  You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

  Unless required by applicable law or agreed to in writing, software
  distributed under the License is distributed on an "AS IS" BASIS,
  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
  See the License for the specific language governing permissions and
  limitations under the License.

*/

pragma solidity 0.6.12;

import { LibEIP712 } from "./LibEIP712.sol";

library LibDelegation {
    struct Delegation {
        address delegatee; // Delegatee
        uint256 nonce; // Nonce
        uint256 expiry; // Expiry
    }

    // Hash for the EIP712 OrderParams Schema
    //    bytes32 constant internal EIP712_DELEGATION_SCHEMA_HASH = keccak256(abi.encodePacked(
    //        "Delegation(",
    //        "address delegatee,",
    //        "uint256 nonce,",
    //        "uint256 expiry",
    //        ")"
    //    ));
    bytes32 internal constant EIP712_DELEGATION_SCHEMA_HASH =
        0xe48329057bfd03d55e49b547132e39cffd9c1820ad7b9d4c5307691425d15adf;

    /// @dev Calculates Keccak-256 hash of the delegation.
    /// @param delegation The delegation structure.
    /// @return delegationHash Keccak-256 EIP712 hash of the delegation.
    function getDelegationHash(Delegation memory delegation, bytes32 eip712ExchangeDomainHash)
        internal
        pure
        returns (bytes32 delegationHash)
    {
        delegationHash = LibEIP712.hashEIP712Message(eip712ExchangeDomainHash, hashDelegation(delegation));
        return delegationHash;
    }

    /// @dev Calculates EIP712 hash of the delegation.
    /// @param delegation The delegation structure.
    /// @return result EIP712 hash of the delegation.
    function hashDelegation(Delegation memory delegation) internal pure returns (bytes32 result) {
        // Assembly for more efficiently computing:
        bytes32 schemaHash = EIP712_DELEGATION_SCHEMA_HASH;

        assembly {
            // Assert delegation offset (this is an internal error that should never be triggered)
            if lt(delegation, 32) {
                invalid()
            }

            // Calculate memory addresses that will be swapped out before hashing
            let pos1 := sub(delegation, 32)

            // Backup
            let temp1 := mload(pos1)

            // Hash in place
            mstore(pos1, schemaHash)
            result := keccak256(pos1, 128)

            // Restore
            mstore(pos1, temp1)
        }
        return result;
    }
}


// SPDX-License-Identifier: MIT
/*

  Copyright 2018 ZeroEx Intl.

  Licensed under the Apache License, Version 2.0 (the "License");
  you may not use this file except in compliance with the License.
  You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

  Unless required by applicable law or agreed to in writing, software
  distributed under the License is distributed on an "AS IS" BASIS,
  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
  See the License for the specific language governing permissions and
  limitations under the License.

*/

pragma solidity 0.6.12;

import { LibEIP712 } from "./LibEIP712.sol";

library LibVoteCast {
    struct VoteCast {
        uint128 proposalId; // Proposal ID
        bool support; // Support
    }

    // Hash for the EIP712 OrderParams Schema
    //    bytes32 constant internal EIP712_VOTE_CAST_SCHEMA_HASH = keccak256(abi.encodePacked(
    //        "VoteCast(",
    //        "uint128 proposalId,",
    //        "bool support",
    //        ")"
    //    ));
    bytes32 internal constant EIP712_VOTE_CAST_SCHEMA_HASH =
        0x4abb8ae9facc09d5584ac64f616551bfc03c3ac63e5c431132305bd9bc8f8246;

    /// @dev Calculates Keccak-256 hash of the vote cast.
    /// @param voteCast The vote cast structure.
    /// @return voteCastHash Keccak-256 EIP712 hash of the vote cast.
    function getVoteCastHash(VoteCast memory voteCast, bytes32 eip712ExchangeDomainHash)
        internal
        pure
        returns (bytes32 voteCastHash)
    {
        voteCastHash = LibEIP712.hashEIP712Message(eip712ExchangeDomainHash, hashVoteCast(voteCast));
        return voteCastHash;
    }

    /// @dev Calculates EIP712 hash of the vote cast.
    /// @param voteCast The vote cast structure.
    /// @return result EIP712 hash of the vote cast.
    function hashVoteCast(VoteCast memory voteCast) internal pure returns (bytes32 result) {
        // Assembly for more efficiently computing:
        bytes32 schemaHash = EIP712_VOTE_CAST_SCHEMA_HASH;

        assembly {
            // Assert vote cast offset (this is an internal error that should never be triggered)
            if lt(voteCast, 32) {
                invalid()
            }

            // Calculate memory addresses that will be swapped out before hashing
            let pos1 := sub(voteCast, 32)

            // Backup
            let temp1 := mload(pos1)

            // Hash in place
            mstore(pos1, schemaHash)
            result := keccak256(pos1, 96)

            // Restore
            mstore(pos1, temp1)
        }
        return result;
    }
}


// SPDX-License-Identifier: MIT
pragma solidity 0.6.12;

/**
 * @dev Wrappers over Solidity's arithmetic operations with added overflow
 * checks.
 *
 * Arithmetic operations in Solidity wrap on overflow. This can easily result
 * in bugs, because programmers usually assume that an overflow raises an
 * error, which is the standard behavior in high level programming languages.
 * `SafeMath` restores this intuition by reverting the transaction when an
 * operation overflows.
 *
 * Using this library instead of the unchecked operations eliminates an entire
 * class of bugs, so it's recommended to use it always.
 */
library SafeMath128 {
    /**
     * @dev Returns the addition of two unsigned integers, reverting on
     * overflow.
     *
     * Counterpart to Solidity's `+` operator.
     *
     * Requirements:
     *
     * - Addition cannot overflow.
     */
    function add(uint128 a, uint128 b) internal pure returns (uint128) {
        uint128 c = a + b;
        require(c >= a, "SafeMath: addition overflow");

        return c;
    }

    /**
     * @dev Returns the subtraction of two unsigned integers, reverting on
     * overflow (when the result is negative).
     *
     * Counterpart to Solidity's `-` operator.
     *
     * Requirements:
     *
     * - Subtraction cannot overflow.
     */
    function sub(uint128 a, uint128 b) internal pure returns (uint128) {
        return sub(a, b, "SafeMath: subtraction overflow");
    }

    /**
     * @dev Returns the subtraction of two unsigned integers, reverting with custom message on
     * overflow (when the result is negative).
     *
     * Counterpart to Solidity's `-` operator.
     *
     * Requirements:
     *
     * - Subtraction cannot overflow.
     */
    function sub(
        uint128 a,
        uint128 b,
        string memory errorMessage
    ) internal pure returns (uint128) {
        require(b <= a, errorMessage);
        uint128 c = a - b;

        return c;
    }

    /**
     * @dev Returns the multiplication of two unsigned integers, reverting on
     * overflow.
     *
     * Counterpart to Solidity's `*` operator.
     *
     * Requirements:
     *
     * - Multiplication cannot overflow.
     */
    function mul(uint128 a, uint128 b) internal pure returns (uint128) {
        // Gas optimization: this is cheaper than requiring 'a' not being zero, but the
        // benefit is lost if 'b' is also tested.
        // See: https://github.com/OpenZeppelin/openzeppelin-contracts/pull/522
        if (a == 0) {
            return 0;
        }

        uint128 c = a * b;
        require(c / a == b, "SafeMath: multiplication overflow");

        return c;
    }

    /**
     * @dev Returns the integer division of two unsigned integers. Reverts on
     * division by zero. The result is rounded towards zero.
     *
     * Counterpart to Solidity's `/` operator. Note: this function uses a
     * `revert` opcode (which leaves remaining gas untouched) while Solidity
     * uses an invalid opcode to revert (consuming all remaining gas).
     *
     * Requirements:
     *
     * - The divisor cannot be zero.
     */
    function div(uint128 a, uint128 b) internal pure returns (uint128) {
        return div(a, b, "SafeMath: division by zero");
    }

    /**
     * @dev Returns the integer division of two unsigned integers. Reverts with custom message on
     * division by zero. The result is rounded towards zero.
     *
     * Counterpart to Solidity's `/` operator. Note: this function uses a
     * `revert` opcode (which leaves remaining gas untouched) while Solidity
     * uses an invalid opcode to revert (consuming all remaining gas).
     *
     * Requirements:
     *
     * - The divisor cannot be zero.
     */
    function div(
        uint128 a,
        uint128 b,
        string memory errorMessage
    ) internal pure returns (uint128) {
        require(b > 0, errorMessage);
        uint128 c = a / b;
        // assert(a == b * c + a % b); // There is no case in which this doesn't hold

        return c;
    }

    /**
     * @dev Returns the remainder of dividing two unsigned integers. (unsigned integer modulo),
     * Reverts when dividing by zero.
     *
     * Counterpart to Solidity's `%` operator. This function uses a `revert`
     * opcode (which leaves remaining gas untouched) while Solidity uses an
     * invalid opcode to revert (consuming all remaining gas).
     *
     * Requirements:
     *
     * - The divisor cannot be zero.
     */
    function mod(uint128 a, uint128 b) internal pure returns (uint128) {
        return mod(a, b, "SafeMath: modulo by zero");
    }

    /**
     * @dev Returns the remainder of dividing two unsigned integers. (unsigned integer modulo),
     * Reverts with custom message when dividing by zero.
     *
     * Counterpart to Solidity's `%` operator. This function uses a `revert`
     * opcode (which leaves remaining gas untouched) while Solidity uses an
     * invalid opcode to revert (consuming all remaining gas).
     *
     * Requirements:
     *
     * - The divisor cannot be zero.
     */
    function mod(
        uint128 a,
        uint128 b,
        string memory errorMessage
    ) internal pure returns (uint128) {
        require(b != 0, errorMessage);
        return a % b;
    }
}

// SPDX-License-Identifier: MIT

pragma solidity ^0.6.0;

/*
 * @dev Provides information about the current execution context, including the
 * sender of the transaction and its data. While these are generally available
 * via msg.sender and msg.data, they should not be accessed in such a direct
 * manner, since when dealing with GSN meta-transactions the account sending and
 * paying for execution may not be the actual sender (as far as an application
 * is concerned).
 *
 * This contract is only required for intermediate, library-like contracts.
 */
abstract contract Context {
    function _msgSender() internal view virtual returns (address payable) {
        return msg.sender;
    }

    function _msgData() internal view virtual returns (bytes memory) {
        this; // silence state mutability warning without generating bytecode - see https://github.com/ethereum/solidity/issues/2691
        return msg.data;
    }
}

// SPDX-License-Identifier: MIT
pragma solidity 0.6.12;
pragma experimental ABIEncoderV2;

/**
 * @title GovernanceDefs
 * @author DerivaDEX
 *
 * This library contains the common structs and enums pertaining to
 * the governance.
 */
library GovernanceDefs {
    struct Proposal {
        bool canceled;
        bool executed;
        address proposer;
        uint32 delay;
        uint96 forVotes;
        uint96 againstVotes;
        uint128 id;
        uint256 eta;
        address[] targets;
        string[] signatures;
        bytes[] calldatas;
        uint256[] values;
        uint256 startBlock;
        uint256 endBlock;
        mapping(address => Receipt) receipts;
    }

    struct Receipt {
        bool hasVoted;
        bool support;
        uint96 votes;
    }

    enum ProposalState { Pending, Active, Canceled, Defeated, Succeeded, Queued, Expired, Executed }
}

// SPDX-License-Identifier: MIT
pragma solidity 0.6.12;
pragma experimental ABIEncoderV2;

library LibDiamondStoragePause {
    struct DiamondStoragePause {
        bool isPaused;
    }

    bytes32 constant DIAMOND_STORAGE_POSITION_PAUSE = keccak256("diamond.standard.diamond.storage.DerivaDEX.Pause");

    function diamondStoragePause() internal pure returns (DiamondStoragePause storage ds) {
        bytes32 position = DIAMOND_STORAGE_POSITION_PAUSE;
        assembly {
            ds_slot := position
        }
    }
}

// SPDX-License-Identifier: MIT
pragma solidity 0.6.12;
pragma experimental ABIEncoderV2;

import { GovernanceDefs } from "../libs/defs/GovernanceDefs.sol";

library LibDiamondStorageGovernance {
    struct DiamondStorageGovernance {
        // Proposal struct by ID
        mapping(uint256 => GovernanceDefs.Proposal) proposals;
        // Latest proposal IDs by proposer address
        mapping(address => uint128) latestProposalIds;
        // Whether transaction hash is currently queued
        mapping(bytes32 => bool) queuedTransactions;
        // Fast path for governance
        mapping(string => bool) fastPathFunctionSignatures;
        // Max number of operations/actions a proposal can have
        uint32 proposalMaxOperations;
        // Number of blocks after a proposal is made that voting begins
        // (e.g. 1 block)
        uint32 votingDelay;
        // Number of blocks voting will be held
        // (e.g. 17280 blocks ~ 3 days of blocks)
        uint32 votingPeriod;
        // Time window (s) a successful proposal must be executed,
        // otherwise will be expired, measured in seconds
        // (e.g. 1209600 seconds)
        uint32 gracePeriod;
        // Minimum time (s) in which a successful proposal must be
        // in the queue before it can be executed
        // (e.g. 0 seconds)
        uint32 minimumDelay;
        // Maximum time (s) in which a successful proposal must be
        // in the queue before it can be executed
        // (e.g. 2592000 seconds ~ 30 days)
        uint32 maximumDelay;
        // Minimum number of for votes required, even if there's a
        // majority in favor
        // (e.g. 2000000e18 ~ 4% of pre-mine DDX supply)
        uint32 quorumVotes;
        // Minimum DDX token holdings required to create a proposal
        // (e.g. 500000e18 ~ 1% of pre-mine DDX supply)
        uint32 proposalThreshold;
        // Number of for or against votes that are necessary to skip
        // the remainder of the voting period
        // (e.g. 25000000e18 tokens/votes)
        uint32 skipRemainingVotingThreshold;
        // Time (s) proposals must be queued before executing
        uint32 timelockDelay;
        // Total number of proposals
        uint128 proposalCount;
    }

    bytes32 constant DIAMOND_STORAGE_POSITION_GOVERNANCE =
        keccak256("diamond.standard.diamond.storage.DerivaDEX.Governance");

    function diamondStorageGovernance() internal pure returns (DiamondStorageGovernance storage ds) {
        bytes32 position = DIAMOND_STORAGE_POSITION_GOVERNANCE;
        assembly {
            ds_slot := position
        }
    }
}


****************************************KEVIN*************************************
// SPDX-License-Identifier: MIT
pragma solidity 0.6.12;
pragma experimental ABIEncoderV2;

import { SafeMath } from "openzeppelin-solidity/contracts/math/SafeMath.sol";
import { LibBytes } from "../libs/LibBytes.sol";
import { LibEIP712 } from "../libs/LibEIP712.sol";
import { LibPermit } from "../libs/LibPermit.sol";
import { SafeMath96 } from "../libs/SafeMath96.sol";
import { IInsuranceFund } from "../facets/interfaces/IInsuranceFund.sol";

/**
 * @title DIFundToken
 * @author DerivaDEX (Borrowed/inspired from Compound)
 * @notice This is the token contract for tokenized DerivaDEX insurance
 *         fund positions. It implements the ERC-20 standard, with
 *         additional functionality around snapshotting user and global
 *         balances.
 * @dev The contract makes use of some nonstandard types not seen in
 *      the ERC-20 standard. The DIFundToken makes frequent use of the
 *      uint96 data type, as opposed to the more standard uint256 type.
 *      Given the maintenance of arrays of balances and allowances, this
 *      allows us to more efficiently pack data together, thereby
 *      resulting in cheaper transactions.
 */
contract DIFundToken {
    using SafeMath96 for uint96;
    using SafeMath for uint256;
    using LibBytes for bytes;

    uint256 internal _totalSupply;

    string private _name;
    string private _symbol;
    string private _version;
    uint8 private _decimals;

    /// @notice Address authorized to issue/mint DDX tokens
    address public issuer;

    mapping(address => mapping(address => uint96)) internal allowances;

    mapping(address => uint96) internal balances;

    /// @notice A checkpoint for marking vote count from given block
    struct Checkpoint {
        uint32 id;
        uint96 values;
    }

    /// @notice A record of votes checkpoints for each account, by index
    mapping(address => mapping(uint256 => Checkpoint)) public checkpoints;

    /// @notice The number of checkpoints for each account
    mapping(address => uint256) public numCheckpoints;

    mapping(uint256 => Checkpoint) totalCheckpoints;

    uint256 numTotalCheckpoints;

    /// @notice A record of states for signing / validating signatures
    mapping(address => uint256) public nonces;

    /// @notice Emitted when a user account's balance changes
    event ValuesChanged(address indexed user, uint96 previousValue, uint96 newValue);

    /// @notice Emitted when a user account's balance changes
    event TotalValuesChanged(uint96 previousValue, uint96 newValue);

    /// @notice Emitted when transfer takes place
    event Transfer(address indexed from, address indexed to, uint256 amount);

    /// @notice Emitted when approval takes place
    event Approval(address indexed owner, address indexed spender, uint256 amount);

    /**
     * @notice Construct a new DIFundToken token
     */
    constructor(
        string memory name,
        string memory symbol,
        uint8 decimals,
        address _issuer
    ) public {
        _name = name;
        _symbol = symbol;
        _decimals = decimals;
        _version = "1";

        // Set issuer to deploying address
        issuer = _issuer;
    }

    /**
     * @notice Returns the name of the token.
     * @return Name of the token.
     */
    function name() public view returns (string memory) {
        return _name;
    }

    /**
     * @notice Returns the symbol of the token.
     * @return Symbol of the token.
     */
    function symbol() public view returns (string memory) {
        return _symbol;
    }

    /**
     * @dev Returns the number of decimals used to get its user representation.
     * For example, if `decimals` equals `2`, a balance of `505` tokens should
     * be displayed to a user as `5,05` (`505 / 10 ** 2`).
     *
     * Tokens usually opt for a value of 18, imitating the relationship between
     * Ether and Wei. This is the value {ERC20} uses, unless {_setupDecimals} is
     * called.
     *
     * NOTE: This information is only used for _display_ purposes: it in
     * no way affects any of the arithmetic of the contract, including
     * {IERC20-balanceOf} and {IERC20-transfer}.
     * @return Number of decimals.
     */
    function decimals() public view returns (uint8) {
        return _decimals;
    }

    /**
     * @notice Approve `spender` to transfer up to `amount` from `src`
     * @dev This will overwrite the approval amount for `spender`
     *  and is subject to issues noted [here](https://eips.ethereum.org/EIPS/eip-20#approve)
     * @param _spender The address of the account which may transfer tokens
     * @param _amount The number of tokens that are approved (2^256-1 means infinite)
     * @return Whether or not the approval succeeded
     */
    function approve(address _spender, uint256 _amount) external returns (bool) {
        require(_spender != address(0), "DIFT: approve to the zero address.");

        // Convert amount to uint96
        uint96 amount;
        if (_amount == uint256(-1)) {
            amount = uint96(-1);
        } else {
            amount = safe96(_amount, "DIFT: amount exceeds 96 bits.");
        }

        // Set allowance
        allowances[msg.sender][_spender] = amount;

        emit Approval(msg.sender, _spender, _amount);
        return true;
    }

    /**
     * @dev Atomically increases the allowance granted to `spender` by the caller.
     * This is an alternative to {approve} that can be used as a mitigation for
     * problems described in {IERC20-approve}.
     * Emits an {Approval} event indicating the updated allowance.
     * Requirements:
     * - `spender` cannot be the zero address.
     */
    function increaseAllowance(address _spender, uint256 _addedValue) external returns (bool) {
        require(_spender != address(0), "DIFT: approve to the zero address.");

        // Convert amount to uint96
        uint96 amount;
        if (_addedValue == uint256(-1)) {
            amount = uint96(-1);
        } else {
            amount = safe96(_addedValue, "DIFT: amount exceeds 96 bits.");
        }

        // Increase allowance
        allowances[msg.sender][_spender] = allowances[msg.sender][_spender].add96(amount);

        emit Approval(msg.sender, _spender, allowances[msg.sender][_spender]);
        return true;
    }

    /**
     * @dev Atomically decreases the allowance granted to `spender` by the caller.
     * This is an alternative to {approve} that can be used as a mitigation for
     * problems described in {IERC20-approve}.
     * Emits an {Approval} event indicating the updated allowance.
     * Requirements:
     * - `spender` cannot be the zero address.
     * - `spender` must have allowance for the caller of at least
     * `subtractedValue`.
     */
    function decreaseAllowance(address _spender, uint256 _subtractedValue) external returns (bool) {
        require(_spender != address(0), "DIFT: approve to the zero address.");

        // Convert amount to uint96
        uint96 amount;
        if (_subtractedValue == uint256(-1)) {
            amount = uint96(-1);
        } else {
            amount = safe96(_subtractedValue, "DIFT: amount exceeds 96 bits.");
        }

        // Decrease allowance
        allowances[msg.sender][_spender] = allowances[msg.sender][_spender].sub96(
            amount,
            "DIFT: decreased allowance below zero."
        );

        emit Approval(msg.sender, _spender, allowances[msg.sender][_spender]);
        return true;
    }

    /**
     * @notice Get the number of tokens held by the `account`
     * @param _account The address of the account to get the balance of
     * @return The number of tokens held
     */
    function balanceOf(address _account) external view returns (uint256) {
        return balances[_account];
    }

    /**
     * @notice Transfer `amount` tokens from `msg.sender` to `dst`
     * @param _recipient The address of the destination account
     * @param _amount The number of tokens to transfer
     * @return Whether or not the transfer succeeded
     */
    function transfer(address _recipient, uint256 _amount) external returns (bool) {
        // Convert amount to uint96
        uint96 amount;
        if (_amount == uint256(-1)) {
            amount = uint96(-1);
        } else {
            amount = safe96(_amount, "DIFT: amount exceeds 96 bits.");
        }

        // Claim DDX rewards on behalf of the sender
        IInsuranceFund(issuer).claimDDXFromInsuranceMining(msg.sender);

        // Claim DDX rewards on behalf of the recipient
        IInsuranceFund(issuer).claimDDXFromInsuranceMining(_recipient);

        // Transfer tokens from sender to recipient
        _transferTokens(msg.sender, _recipient, amount);

        return true;
    }

    /**
     * @notice Transfer `amount` tokens from `src` to `dst`
     * @param _sender The address of the source account
     * @param _recipient The address of the destination account
     * @param _amount The number of tokens to transfer
     * @return Whether or not the transfer succeeded
     */
    function transferFrom(
        address _sender,
        address _recipient,
        uint256 _amount
    ) external returns (bool) {
        uint96 spenderAllowance = allowances[_sender][msg.sender];

        // Convert amount to uint96
        uint96 amount;
        if (_amount == uint256(-1)) {
            amount = uint96(-1);
        } else {
            amount = safe96(_amount, "DIFT: amount exceeds 96 bits.");
        }

        if (msg.sender != _sender && spenderAllowance != uint96(-1)) {
            // Tx sender is not the same as transfer sender and doesn't
            // have unlimited allowance.
            // Reduce allowance by amount being transferred
            uint96 newAllowance = spenderAllowance.sub96(amount);
            allowances[_sender][msg.sender] = newAllowance;

            emit Approval(_sender, msg.sender, newAllowance);
        }

        // Claim DDX rewards on behalf of the sender
        IInsuranceFund(issuer).claimDDXFromInsuranceMining(_sender);

        // Claim DDX rewards on behalf of the recipient
        IInsuranceFund(issuer).claimDDXFromInsuranceMining(_recipient);

        // Transfer tokens from sender to recipient
        _transferTokens(_sender, _recipient, amount);

        return true;
    }

    /**
     * @dev Creates `amount` tokens and assigns them to `account`, increasing
     *      the total supply.
     *
     * Emits a {Transfer} event with `from` set to the zero address.
     *
     * Requirements
     *
     * - `to` cannot be the zero address.
     */
    function mint(address _recipient, uint256 _amount) external {
        require(msg.sender == issuer, "DIFT: unauthorized mint.");

        // Convert amount to uint96
        uint96 amount;
        if (_amount == uint256(-1)) {
            amount = uint96(-1);
        } else {
            amount = safe96(_amount, "DIFT: amount exceeds 96 bits.");
        }

        // Mint tokens to recipient
        _transferTokensMint(_recipient, amount);
    }

    /**
     * @dev Creates `amount` tokens and assigns them to `account`, decreasing
     *      the total supply.
     *
     * Emits a {Transfer} event with `from` set to the zero address.
     *
     * Requirements
     *
     * - `to` cannot be the zero address.
     */
    function burn(uint256 _amount) external {
        // Convert amount to uint96
        uint96 amount;
        if (_amount == uint256(-1)) {
            amount = uint96(-1);
        } else {
            amount = safe96(_amount, "DIFT: amount exceeds 96 bits.");
        }

        // Burn tokens from sender
        _transferTokensBurn(msg.sender, amount);
    }

    /**
     * @dev Creates `amount` tokens and assigns them to `account`, increasing
     *      the total supply.
     *
     * Emits a {Transfer} event with `from` set to the zero address.
     *
     * Requirements
     *
     * - `to` cannot be the zero address.
     */
    function burnFrom(address _account, uint256 _amount) external {
        uint96 spenderAllowance = allowances[_account][msg.sender];

        // Convert amount to uint96
        uint96 amount;
        if (_amount == uint256(-1)) {
            amount = uint96(-1);
        } else {
            amount = safe96(_amount, "DIFT: amount exceeds 96 bits.");
        }

        if (msg.sender != _account && spenderAllowance != uint96(-1) && msg.sender != issuer) {
            // Tx sender is not the same as burn account and doesn't
            // have unlimited allowance.
            // Reduce allowance by amount being transferred
            uint96 newAllowance = spenderAllowance.sub96(amount, "DIFT: burn amount exceeds allowance.");
            allowances[_account][msg.sender] = newAllowance;

            emit Approval(_account, msg.sender, newAllowance);
        }

        // Burn tokens from account
        _transferTokensBurn(_account, amount);
    }

    /**
     * @notice Permits allowance from signatory to `spender`
     * @param _spender The spender being approved
     * @param _value The value being approved
     * @param _nonce The contract state required to match the signature
     * @param _expiry The time at which to expire the signature
     * @param _signature Signature
     */
    function permit(
        address _spender,
        uint256 _value,
        uint256 _nonce,
        uint256 _expiry,
        bytes memory _signature
    ) external {
        // Perform EIP712 hashing logic
        bytes32 eip712OrderParamsDomainHash = LibEIP712.hashEIP712Domain(_name, _version, getChainId(), address(this));
        bytes32 permitHash =
            LibPermit.getPermitHash(
                LibPermit.Permit({ spender: _spender, value: _value, nonce: _nonce, expiry: _expiry }),
                eip712OrderParamsDomainHash
            );

        // Perform sig recovery
        uint8 v = uint8(_signature[0]);
        bytes32 r = _signature.readBytes32(1);
        bytes32 s = _signature.readBytes32(33);

        // EIP-2 still allows signature malleability for ecrecover(). Remove this possibility and make the signature
        // unique. Appendix F in the Ethereum Yellow paper (https://ethereum.github.io/yellowpaper/paper.pdf), defines
        // the valid range for s in (281): 0 < s < secp256k1n ÷ 2 + 1, and for v in (282): v ∈ {27, 28}. Most
        // signatures from current libraries generate a unique signature with an s-value in the lower half order.
        //
        // If your library generates malleable signatures, such as s-values in the upper range, calculate a new s-value
        // with 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141 - s1 and flip v from 27 to 28 or
        // vice versa. If your library also generates signatures with 0/1 for v instead 27/28, add 27 to v to accept
        // these malleable signatures as well.
        if (uint256(s) > 0x7FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF5D576E7357A4501DDFE92F46681B20A0) {
            revert("ECDSA: invalid signature 's' value");
        }

        if (v != 27 && v != 28) {
            revert("ECDSA: invalid signature 'v' value");
        }

        address recovered = ecrecover(permitHash, v, r, s);

        require(recovered != address(0), "DIFT: invalid signature.");
        require(_nonce == nonces[recovered]++, "DIFT: invalid nonce.");
        require(block.timestamp <= _expiry, "DIFT: signature expired.");

        // Convert amount to uint96
        uint96 amount;
        if (_value == uint256(-1)) {
            amount = uint96(-1);
        } else {
            amount = safe96(_value, "DIFT: amount exceeds 96 bits.");
        }

        // Set allowance
        allowances[recovered][_spender] = amount;
        emit Approval(recovered, _spender, _value);
    }

    /**
     * @notice Get the number of tokens `spender` is approved to spend on behalf of `account`
     * @param _account The address of the account holding the funds
     * @param _spender The address of the account spending the funds
     * @return The number of tokens approved
     */
    function allowance(address _account, address _spender) external view returns (uint256) {
        return allowances[_account][_spender];
    }

    /**
     * @notice Get the total max supply of DDX tokens
     * @return The total max supply of DDX
     */
    function totalSupply() external view returns (uint256) {
        return _totalSupply;
    }

    /**
     * @notice Determine the prior number of values for an account as of a block number
     * @dev Block number must be a finalized block or else this function will revert to prevent misinformation.
     * @param _account The address of the account to check
     * @param _blockNumber The block number to get the vote balance at
     * @return The number of values the account had as of the given block
     */
    function getPriorValues(address _account, uint256 _blockNumber) external view returns (uint96) {
        require(_blockNumber < block.number, "DIFT: block not yet determined.");

        uint256 numCheckpointsAccount = numCheckpoints[_account];
        if (numCheckpointsAccount == 0) {
            return 0;
        }

        // First check most recent balance
        if (checkpoints[_account][numCheckpointsAccount - 1].id <= _blockNumber) {
            return checkpoints[_account][numCheckpointsAccount - 1].values;
        }

        // Next check implicit zero balance
        if (checkpoints[_account][0].id > _blockNumber) {
            return 0;
        }

        // Perform binary search to find the most recent token holdings
        uint256 lower = 0;
        uint256 upper = numCheckpointsAccount - 1;
        while (upper > lower) {
            // ceil, avoiding overflow
            uint256 center = upper - (upper - lower) / 2;
            Checkpoint memory cp = checkpoints[_account][center];
            if (cp.id == _blockNumber) {
                return cp.values;
            } else if (cp.id < _blockNumber) {
                lower = center;
            } else {
                upper = center - 1;
            }
        }
        return checkpoints[_account][lower].values;
    }

    /**
     * @notice Determine the prior number of values for an account as of a block number
     * @dev Block number must be a finalized block or else this function will revert to prevent misinformation.
     * @param _blockNumber The block number to get the vote balance at
     * @return The number of values the account had as of the given block
     */
    function getTotalPriorValues(uint256 _blockNumber) external view returns (uint96) {
        require(_blockNumber < block.number, "DIFT: block not yet determined.");

        if (numTotalCheckpoints == 0) {
            return 0;
        }

        // First check most recent balance
        if (totalCheckpoints[numTotalCheckpoints - 1].id <= _blockNumber) {
            return totalCheckpoints[numTotalCheckpoints - 1].values;
        }

        // Next check implicit zero balance
        if (totalCheckpoints[0].id > _blockNumber) {
            return 0;
        }

        // Perform binary search to find the most recent token holdings
        // leading to a measure of voting power
        uint256 lower = 0;
        uint256 upper = numTotalCheckpoints - 1;
        while (upper > lower) {
            // ceil, avoiding overflow
            uint256 center = upper - (upper - lower) / 2;
            Checkpoint memory cp = totalCheckpoints[center];
            if (cp.id == _blockNumber) {
                return cp.values;
            } else if (cp.id < _blockNumber) {
                lower = center;
            } else {
                upper = center - 1;
            }
        }
        return totalCheckpoints[lower].values;
    }

    function _transferTokens(
        address _spender,
        address _recipient,
        uint96 _amount
    ) internal {
        require(_spender != address(0), "DIFT: cannot transfer from the zero address.");
        require(_recipient != address(0), "DIFT: cannot transfer to the zero address.");

        // Reduce spender's balance and increase recipient balance
        balances[_spender] = balances[_spender].sub96(_amount);
        balances[_recipient] = balances[_recipient].add96(_amount);
        emit Transfer(_spender, _recipient, _amount);

        // Move values from spender to recipient
        _moveTokens(_spender, _recipient, _amount);
    }

    function _transferTokensMint(address _recipient, uint96 _amount) internal {
        require(_recipient != address(0), "DIFT: cannot transfer to the zero address.");

        // Add to recipient's balance
        balances[_recipient] = balances[_recipient].add96(_amount);

        _totalSupply = _totalSupply.add(_amount);

        emit Transfer(address(0), _recipient, _amount);

        // Add value to recipient's checkpoint
        _moveTokens(address(0), _recipient, _amount);
        _writeTotalCheckpoint(_amount, true);
    }

    function _transferTokensBurn(address _spender, uint96 _amount) internal {
        require(_spender != address(0), "DIFT: cannot transfer from the zero address.");

        // Reduce the spender/burner's balance
        balances[_spender] = balances[_spender].sub96(_amount, "DIFT: not enough balance to burn.");

        // Reduce the circulating supply
        _totalSupply = _totalSupply.sub(_amount);
        emit Transfer(_spender, address(0), _amount);

        // Reduce value from spender's checkpoint
        _moveTokens(_spender, address(0), _amount);
        _writeTotalCheckpoint(_amount, false);
    }

    function _moveTokens(
        address _initUser,
        address _finUser,
        uint96 _amount
    ) internal {
        if (_initUser != _finUser && _amount > 0) {
            // Initial user address is different than final
            // user address and nonzero number of values moved
            if (_initUser != address(0)) {
                uint256 initUserNum = numCheckpoints[_initUser];

                // Retrieve and compute the old and new initial user
                // address' values
                uint96 initUserOld = initUserNum > 0 ? checkpoints[_initUser][initUserNum - 1].values : 0;
                uint96 initUserNew = initUserOld.sub96(_amount);
                _writeCheckpoint(_initUser, initUserOld, initUserNew);
            }

            if (_finUser != address(0)) {
                uint256 finUserNum = numCheckpoints[_finUser];

                // Retrieve and compute the old and new final user
                // address' values
                uint96 finUserOld = finUserNum > 0 ? checkpoints[_finUser][finUserNum - 1].values : 0;
                uint96 finUserNew = finUserOld.add96(_amount);
                _writeCheckpoint(_finUser, finUserOld, finUserNew);
            }
        }
    }

    function _writeCheckpoint(
        address _user,
        uint96 _oldValues,
        uint96 _newValues
    ) internal {
        uint32 blockNumber = safe32(block.number, "DIFT: exceeds 32 bits.");
        uint256 userNum = numCheckpoints[_user];
        if (userNum > 0 && checkpoints[_user][userNum - 1].id == blockNumber) {
            // If latest checkpoint is current block, edit in place
            checkpoints[_user][userNum - 1].values = _newValues;
        } else {
            // Create a new id, value pair
            checkpoints[_user][userNum] = Checkpoint({ id: blockNumber, values: _newValues });
            numCheckpoints[_user] = userNum.add(1);
        }

        emit ValuesChanged(_user, _oldValues, _newValues);
    }

    function _writeTotalCheckpoint(uint96 _amount, bool increase) internal {
        if (_amount > 0) {
            uint32 blockNumber = safe32(block.number, "DIFT: exceeds 32 bits.");
            uint96 oldValues = numTotalCheckpoints > 0 ? totalCheckpoints[numTotalCheckpoints - 1].values : 0;
            uint96 newValues = increase ? oldValues.add96(_amount) : oldValues.sub96(_amount);

            if (numTotalCheckpoints > 0 && totalCheckpoints[numTotalCheckpoints - 1].id == block.number) {
                // If latest checkpoint is current block, edit in place
                totalCheckpoints[numTotalCheckpoints - 1].values = newValues;
            } else {
                // Create a new id, value pair
                totalCheckpoints[numTotalCheckpoints].id = blockNumber;
                totalCheckpoints[numTotalCheckpoints].values = newValues;
                numTotalCheckpoints = numTotalCheckpoints.add(1);
            }

            emit TotalValuesChanged(oldValues, newValues);
        }
    }

    function safe32(uint256 n, string memory errorMessage) internal pure returns (uint32) {
        require(n < 2**32, errorMessage);
        return uint32(n);
    }

    function safe96(uint256 n, string memory errorMessage) internal pure returns (uint96) {
        require(n < 2**96, errorMessage);
        return uint96(n);
    }

    function getChainId() internal pure returns (uint256) {
        uint256 chainId;
        assembly {
            chainId := chainid()
        }
        return chainId;
    }
}


// SPDX-License-Identifier: MIT

pragma solidity ^0.6.0;

import "../GSN/Context.sol";
/**
 * @dev Contract module which provides a basic access control mechanism, where
 * there is an account (an owner) that can be granted exclusive access to
 * specific functions.
 *
 * By default, the owner account will be the one that deploys the contract. This
 * can later be changed with {transferOwnership}.
 *
 * This module is used through inheritance. It will make available the modifier
 * `onlyOwner`, which can be applied to your functions to restrict their use to
 * the owner.
 */
contract Ownable is Context {
    address private _owner;

    event OwnershipTransferred(address indexed previousOwner, address indexed newOwner);

    /**
     * @dev Initializes the contract setting the deployer as the initial owner.
     */
    constructor () internal {
        address msgSender = _msgSender();
        _owner = msgSender;
        emit OwnershipTransferred(address(0), msgSender);
    }

    /**
     * @dev Returns the address of the current owner.
     */
    function owner() public view returns (address) {
        return _owner;
    }

    /**
     * @dev Throws if called by any account other than the owner.
     */
    modifier onlyOwner() {
        require(_owner == _msgSender(), "Ownable: caller is not the owner");
        _;
    }

    /**
     * @dev Leaves the contract without owner. It will not be possible to call
     * `onlyOwner` functions anymore. Can only be called by the current owner.
     *
     * NOTE: Renouncing ownership will leave the contract without an owner,
     * thereby removing any functionality that is only available to the owner.
     */
    function renounceOwnership() public virtual onlyOwner {
        emit OwnershipTransferred(_owner, address(0));
        _owner = address(0);
    }

    /**
     * @dev Transfers ownership of the contract to a new account (`newOwner`).
     * Can only be called by the current owner.
     */
    function transferOwnership(address newOwner) public virtual onlyOwner {
        require(newOwner != address(0), "Ownable: new owner is the zero address");
        emit OwnershipTransferred(_owner, newOwner);
        _owner = newOwner;
    }
}



// SPDX-License-Identifier: MIT
/**
 *Submitted for verification at Etherscan.io on 2019-07-18
 */

pragma solidity 0.6.12;

import { SafeMath } from "openzeppelin-solidity/contracts/math/SafeMath.sol";
import { Ownable } from "openzeppelin-solidity/contracts/access/Ownable.sol";
import { IERC20 } from "openzeppelin-solidity/contracts/token/ERC20/IERC20.sol";

library Roles {
    struct Role {
        mapping(address => bool) bearer;
    }

    function add(Role storage role, address account) internal {
        require(!has(role, account), "Roles: account already has role");
        role.bearer[account] = true;
    }

    function remove(Role storage role, address account) internal {
        require(has(role, account), "Roles: account does not have role");
        role.bearer[account] = false;
    }

    function has(Role storage role, address account) internal view returns (bool) {
        require(account != address(0), "Roles: account is the zero address");
        return role.bearer[account];
    }
}

contract PauserRole is Ownable {
    using Roles for Roles.Role;

    Roles.Role private _pausers;

    event PauserAdded(address indexed account);

    event PauserRemoved(address indexed account);

    constructor() internal {
        _addPauser(msg.sender);
    }

    modifier onlyPauser() {
        require(isPauser(msg.sender), "PauserRole: caller does not have the Pauser role");
        _;
    }

    function isPauser(address account) public view returns (bool) {
        return _pausers.has(account);
    }

    function addPauser(address account) public onlyOwner {
        _addPauser(account);
    }

    function removePauser(address account) public onlyOwner {
        _removePauser(account);
    }

    function renouncePauser() public {
        _removePauser(msg.sender);
    }

    function _addPauser(address account) internal {
        _pausers.add(account);
        emit PauserAdded(account);
    }

    function _removePauser(address account) internal {
        _pausers.remove(account);
        emit PauserRemoved(account);
    }
}

contract Pausable is PauserRole {
    bool private _paused;

    event Paused(address account);

    event Unpaused(address account);

    constructor() internal {
        _paused = false;
    }

    function paused() public view returns (bool) {
        return _paused;
    }

    modifier whenNotPaused() {
        require(!_paused, "Pausable: paused");
        _;
    }

    modifier whenPaused() {
        require(_paused, "Pausable: not paused");
        _;
    }

    function pause() public onlyPauser whenNotPaused {
        _paused = true;
        emit Paused(msg.sender);
    }

    function unpause() public onlyPauser whenPaused {
        _paused = false;
        emit Unpaused(msg.sender);
    }
}

contract ERC20 is IERC20, Ownable {
    using SafeMath for uint256;

    mapping(address => uint256) private _balances;

    mapping(address => mapping(address => uint256)) private _allowances;

    uint256 private _totalSupply;

    event Issue(address indexed account, uint256 amount);

    event Redeem(address indexed account, uint256 value);

    function totalSupply() public view override returns (uint256) {
        return _totalSupply;
    }

    function balanceOf(address account) public view override returns (uint256) {
        return _balances[account];
    }

    function transfer(address recipient, uint256 amount) public virtual override returns (bool) {
        _transfer(msg.sender, recipient, amount);
        return true;
    }

    function allowance(address owner, address spender) public view override returns (uint256) {
        return _allowances[owner][spender];
    }

    function approve(address spender, uint256 value) public virtual override returns (bool) {
        _approve(msg.sender, spender, value);
        return true;
    }

    function transferFrom(
        address sender,
        address recipient,
        uint256 amount
    ) public virtual override returns (bool) {
        _transfer(sender, recipient, amount);
        _approve(sender, msg.sender, _allowances[sender][msg.sender].sub(amount));
        return true;
    }

    function increaseAllowance(address spender, uint256 addedValue) public virtual returns (bool) {
        _approve(msg.sender, spender, _allowances[msg.sender][spender].add(addedValue));
        return true;
    }

    function decreaseAllowance(address spender, uint256 subtractedValue) public virtual returns (bool) {
        _approve(msg.sender, spender, _allowances[msg.sender][spender].sub(subtractedValue));
        return true;
    }

    function _transfer(
        address sender,
        address recipient,
        uint256 amount
    ) internal {
        require(sender != address(0), "ERC20: transfer from the zero address");
        require(recipient != address(0), "ERC20: transfer to the zero address");

        _balances[sender] = _balances[sender].sub(amount);
        _balances[recipient] = _balances[recipient].add(amount);
        emit Transfer(sender, recipient, amount);
    }

    function _approve(
        address owner,
        address spender,
        uint256 value
    ) internal {
        require(owner != address(0), "ERC20: approve from the zero address");
        require(spender != address(0), "ERC20: approve to the zero address");

        _allowances[owner][spender] = value;
        emit Approval(owner, spender, value);
    }

    function _issue(address account, uint256 amount) internal {
        require(account != address(0), "CoinFactory: issue to the zero address");

        _totalSupply = _totalSupply.add(amount);
        _balances[account] = _balances[account].add(amount);
        emit Transfer(address(0), account, amount);
        emit Issue(account, amount);
    }

    function _redeem(address account, uint256 value) internal {
        require(account != address(0), "CoinFactory: redeem from the zero address");

        _totalSupply = _totalSupply.sub(value);
        _balances[account] = _balances[account].sub(value);
        emit Transfer(account, address(0), value);
        emit Redeem(account, value);
    }
}

contract ERC20Pausable is ERC20, Pausable {
    function transfer(address to, uint256 value) public virtual override whenNotPaused returns (bool) {
        return super.transfer(to, value);
    }

    function transferFrom(
        address from,
        address to,
        uint256 value
    ) public virtual override whenNotPaused returns (bool) {
        return super.transferFrom(from, to, value);
    }

    function approve(address spender, uint256 value) public virtual override whenNotPaused returns (bool) {
        return super.approve(spender, value);
    }

    function increaseAllowance(address spender, uint256 addedValue)
        public
        virtual
        override
        whenNotPaused
        returns (bool)
    {
        return super.increaseAllowance(spender, addedValue);
    }

    function decreaseAllowance(address spender, uint256 subtractedValue)
        public
        virtual
        override
        whenNotPaused
        returns (bool)
    {
        return super.decreaseAllowance(spender, subtractedValue);
    }
}

contract CoinFactoryAdminRole is Ownable {
    using Roles for Roles.Role;

    event CoinFactoryAdminRoleAdded(address indexed account);

    event CoinFactoryAdminRoleRemoved(address indexed account);

    Roles.Role private _coinFactoryAdmins;

    constructor() internal {
        _addCoinFactoryAdmin(msg.sender);
    }

    modifier onlyCoinFactoryAdmin() {
        require(isCoinFactoryAdmin(msg.sender), "CoinFactoryAdminRole: caller does not have the CoinFactoryAdmin role");
        _;
    }

    function isCoinFactoryAdmin(address account) public view returns (bool) {
        return _coinFactoryAdmins.has(account);
    }

    function addCoinFactoryAdmin(address account) public onlyOwner {
        _addCoinFactoryAdmin(account);
    }

    function removeCoinFactoryAdmin(address account) public onlyOwner {
        _removeCoinFactoryAdmin(account);
    }

    function renounceCoinFactoryAdmin() public {
        _removeCoinFactoryAdmin(msg.sender);
    }

    function _addCoinFactoryAdmin(address account) internal {
        _coinFactoryAdmins.add(account);
        emit CoinFactoryAdminRoleAdded(account);
    }

    function _removeCoinFactoryAdmin(address account) internal {
        _coinFactoryAdmins.remove(account);
        emit CoinFactoryAdminRoleRemoved(account);
    }
}

contract CoinFactory is ERC20, CoinFactoryAdminRole {
    function issue(address account, uint256 amount) public onlyCoinFactoryAdmin returns (bool) {
        _issue(account, amount);
        return true;
    }

    function redeem(address account, uint256 amount) public onlyCoinFactoryAdmin returns (bool) {
        _redeem(account, amount);
        return true;
    }
}

contract BlacklistAdminRole is Ownable {
    using Roles for Roles.Role;

    event BlacklistAdminAdded(address indexed account);
    event BlacklistAdminRemoved(address indexed account);

    Roles.Role private _blacklistAdmins;

    constructor() internal {
        _addBlacklistAdmin(msg.sender);
    }

    modifier onlyBlacklistAdmin() {
        require(isBlacklistAdmin(msg.sender), "BlacklistAdminRole: caller does not have the BlacklistAdmin role");
        _;
    }

    function isBlacklistAdmin(address account) public view returns (bool) {
        return _blacklistAdmins.has(account);
    }

    function addBlacklistAdmin(address account) public onlyOwner {
        _addBlacklistAdmin(account);
    }

    function removeBlacklistAdmin(address account) public onlyOwner {
        _removeBlacklistAdmin(account);
    }

    function renounceBlacklistAdmin() public {
        _removeBlacklistAdmin(msg.sender);
    }

    function _addBlacklistAdmin(address account) internal {
        _blacklistAdmins.add(account);
        emit BlacklistAdminAdded(account);
    }

    function _removeBlacklistAdmin(address account) internal {
        _blacklistAdmins.remove(account);
        emit BlacklistAdminRemoved(account);
    }
}

contract Blacklist is ERC20, BlacklistAdminRole {
    mapping(address => bool) private _blacklist;

    event BlacklistAdded(address indexed account);

    event BlacklistRemoved(address indexed account);

    function addBlacklist(address[] memory accounts) public onlyBlacklistAdmin returns (bool) {
        for (uint256 i = 0; i < accounts.length; i++) {
            _addBlacklist(accounts[i]);
        }
    }

    function removeBlacklist(address[] memory accounts) public onlyBlacklistAdmin returns (bool) {
        for (uint256 i = 0; i < accounts.length; i++) {
            _removeBlacklist(accounts[i]);
        }
    }

    function isBlacklist(address account) public view returns (bool) {
        return _blacklist[account];
    }

    function _addBlacklist(address account) internal {
        _blacklist[account] = true;
        emit BlacklistAdded(account);
    }

    function _removeBlacklist(address account) internal {
        _blacklist[account] = false;
        emit BlacklistRemoved(account);
    }
}

contract HDUMToken is ERC20, ERC20Pausable, CoinFactory, Blacklist {
    string public name;
    string public symbol;
    uint8 public decimals;
    uint256 private _totalSupply;

    constructor(
        string memory _name,
        string memory _symbol,
        uint8 _decimals
    ) public {
        _totalSupply = 0;
        name = _name;
        symbol = _symbol;
        decimals = _decimals;
    }

    function transfer(address to, uint256 value) public override(ERC20, ERC20Pausable) whenNotPaused returns (bool) {
        require(!isBlacklist(msg.sender), "HDUMToken: caller in blacklist can't transfer");
        require(!isBlacklist(to), "HDUMToken: not allow to transfer to recipient address in blacklist");
        return super.transfer(to, value);
    }

    function transferFrom(
        address from,
        address to,
        uint256 value
    ) public override(ERC20, ERC20Pausable) whenNotPaused returns (bool) {
        require(!isBlacklist(msg.sender), "HDUMToken: caller in blacklist can't transferFrom");
        require(!isBlacklist(from), "HDUMToken: from in blacklist can't transfer");
        require(!isBlacklist(to), "HDUMToken: not allow to transfer to recipient address in blacklist");
        return super.transferFrom(from, to, value);
    }

    function approve(address spender, uint256 value) public virtual override(ERC20, ERC20Pausable) returns (bool) {
        return super.approve(spender, value);
    }

    function increaseAllowance(address spender, uint256 addedValue)
        public
        virtual
        override(ERC20, ERC20Pausable)
        returns (bool)
    {
        return super.increaseAllowance(spender, addedValue);
    }

    function decreaseAllowance(address spender, uint256 subtractedValue)
        public
        virtual
        override(ERC20, ERC20Pausable)
        returns (bool)
    {
        return super.decreaseAllowance(spender, subtractedValue);
    }
}





// SPDX-License-Identifier: MIT
pragma solidity 0.6.12;

import { LibDiamondStorageDerivaDEX } from "../storage/LibDiamondStorageDerivaDEX.sol";
import { LibDiamondStorage } from "../diamond/LibDiamondStorage.sol";
import { IERC165 } from "./IERC165.sol";

contract OwnershipFacet {
    event OwnershipTransferred(address indexed previousOwner, address indexed newOwner);

    /**
     * @notice This function transfers ownership to self. This is done
     *         so that we can ensure upgrades (using diamondCut) and
     *         various other critical parameter changing scenarios
     *         can only be done via governance (a facet).
     */
    function transferOwnershipToSelf() external {
        LibDiamondStorageDerivaDEX.DiamondStorageDerivaDEX storage dsDerivaDEX =
            LibDiamondStorageDerivaDEX.diamondStorageDerivaDEX();
        require(msg.sender == dsDerivaDEX.admin, "Not authorized");
        dsDerivaDEX.admin = address(this);

        emit OwnershipTransferred(msg.sender, address(this));
    }

    /**
     * @notice This gets the admin for the diamond.
     * @return Admin address.
     */
    function getAdmin() external view returns (address) {
        LibDiamondStorageDerivaDEX.DiamondStorageDerivaDEX storage dsDerivaDEX =
            LibDiamondStorageDerivaDEX.diamondStorageDerivaDEX();
        return dsDerivaDEX.admin;
    }
}

// SPDX-License-Identifier: MIT
pragma solidity 0.6.12;
pragma experimental ABIEncoderV2;

import { IDDX } from "./interfaces/IDDX.sol";

/**
 * @title DDXWalletCloneable
 * @author DerivaDEX
 * @notice This is a cloneable on-chain DDX wallet that holds a trader's
 *         stakes and issued rewards.
 */
contract DDXWalletCloneable {
    // Whether contract has already been initialized once before
    bool initialized;

    /**
     * @notice This function initializes the on-chain DDX wallet
     *         for a given trader.
     * @param _trader Trader address.
     * @param _ddxToken DDX token address.
     * @param _derivaDEX DerivaDEX Proxy address.
     */
    function initialize(
        address _trader,
        IDDX _ddxToken,
        address _derivaDEX
    ) external {
        // Prevent initializing more than once
        require(!initialized, "DDXWalletCloneable: already init.");
        initialized = true;

        // Automatically delegate the holdings of this contract/wallet
        // back to the trader.
        _ddxToken.delegate(_trader);

        // Approve the DerivaDEX Proxy contract for unlimited transfers
        _ddxToken.approve(_derivaDEX, uint96(-1));
    }
}



// SPDX-License-Identifier: MIT
pragma solidity 0.6.12;
pragma experimental ABIEncoderV2;

import { DIFundToken } from "../DIFundToken.sol";

/**
 * @title DIFundToken
 * @author DerivaDEX (Borrowed/inspired from Compound)
 * @notice This is the token contract for tokenized DerivaDEX insurance
 *         fund positions. It implements the ERC-20 standard, with
 *         additional functionality around snapshotting user and global
 *         balances.
 * @dev The contract makes use of some nonstandard types not seen in
 *      the ERC-20 standard. The DIFundToken makes frequent use of the
 *      uint96 data type, as opposed to the more standard uint256 type.
 *      Given the maintenance of arrays of balances and allowances, this
 *      allows us to more efficiently pack data together, thereby
 *      resulting in cheaper transactions.
 */
interface IDIFundTokenFactory {
    function createNewDIFundToken(
        string calldata _name,
        string calldata _symbol,
        uint8 _decimals
    ) external returns (address);

    function diFundTokens(uint256 index) external returns (DIFundToken);

    function issuer() external view returns (address);

    function getDIFundTokens() external view returns (DIFundToken[] memory);

    function getDIFundTokensLength() external view returns (uint256);
}


// SPDX-License-Identifier: MIT
pragma solidity 0.6.12;
pragma experimental ABIEncoderV2;

import { SafeMath } from "openzeppelin-solidity/contracts/math/SafeMath.sol";
import { LibBytes } from "../libs/LibBytes.sol";
import { LibEIP712 } from "../libs/LibEIP712.sol";
import { LibPermit } from "../libs/LibPermit.sol";
import { SafeMath96 } from "../libs/SafeMath96.sol";
import { DIFundToken } from "./DIFundToken.sol";

/**
 * @title DIFundTokenFactory
 * @author DerivaDEX (Borrowed/inspired from Compound)
 * @notice This is the native token contract for DerivaDEX. It
 *         implements the ERC-20 standard, with additional
 *         functionality to efficiently handle the governance aspect of
 *         the DerivaDEX ecosystem.
 * @dev The contract makes use of some nonstandard types not seen in
 *      the ERC-20 standard. The DDX token makes frequent use of the
 *      uint96 data type, as opposed to the more standard uint256 type.
 *      Given the maintenance of arrays of balances, allowances, and
 *      voting checkpoints, this allows us to more efficiently pack
 *      data together, thereby resulting in cheaper transactions.
 */
contract DIFundTokenFactory {
    DIFundToken[] public diFundTokens;

    address public issuer;

    /**
     * @notice Construct a new DDX token
     */
    constructor(address _issuer) public {
        // Set issuer to deploying address
        issuer = _issuer;
    }

    function createNewDIFundToken(
        string calldata _name,
        string calldata _symbol,
        uint8 _decimals
    ) external returns (address) {
        require(msg.sender == issuer, "DIFTF: unauthorized.");
        DIFundToken diFundToken = new DIFundToken(_name, _symbol, _decimals, issuer);
        diFundTokens.push(diFundToken);
        return address(diFundToken);
    }

    function getDIFundTokens() external view returns (DIFundToken[] memory) {
        return diFundTokens;
    }

    function getDIFundTokensLength() external view returns (uint256) {
        return diFundTokens.length;
    }
}


// SPDX-License-Identifier: MIT
pragma solidity 0.6.12;
pragma experimental ABIEncoderV2;

import { SafeMath } from "openzeppelin-solidity/contracts/math/SafeMath.sol";
import { LibBytes } from "../libs/LibBytes.sol";
import { LibEIP712 } from "../libs/LibEIP712.sol";
import { LibDelegation } from "../libs/LibDelegation.sol";
import { LibPermit } from "../libs/LibPermit.sol";
import { SafeMath96 } from "../libs/SafeMath96.sol";

/**
 * @title DDX
 * @author DerivaDEX (Borrowed/inspired from Compound)
 * @notice This is the native token contract for DerivaDEX. It
 *         implements the ERC-20 standard, with additional
 *         functionality to efficiently handle the governance aspect of
 *         the DerivaDEX ecosystem.
 * @dev The contract makes use of some nonstandard types not seen in
 *      the ERC-20 standard. The DDX token makes frequent use of the
 *      uint96 data type, as opposed to the more standard uint256 type.
 *      Given the maintenance of arrays of balances, allowances, and
 *      voting checkpoints, this allows us to more efficiently pack
 *      data together, thereby resulting in cheaper transactions.
 */
contract DDX {
    using SafeMath96 for uint96;
    using SafeMath for uint256;
    using LibBytes for bytes;

    /// @notice ERC20 token name for this token
    string public constant name = "DerivaDAO"; // solhint-disable-line const-name-snakecase

    /// @notice ERC20 token symbol for this token
    string public constant symbol = "DDX"; // solhint-disable-line const-name-snakecase

    /// @notice ERC20 token decimals for this token
    uint8 public constant decimals = 18; // solhint-disable-line const-name-snakecase

    /// @notice Version number for this token. Used for EIP712 hashing.
    string public constant version = "1"; // solhint-disable-line const-name-snakecase

    /// @notice Max number of tokens to be issued (100 million DDX)
    uint96 public constant MAX_SUPPLY = 100000000e18;

    /// @notice Total number of tokens in circulation (50 million DDX)
    uint96 public constant PRE_MINE_SUPPLY = 50000000e18;

    /// @notice Issued supply of tokens
    uint96 public issuedSupply;

    /// @notice Current total/circulating supply of tokens
    uint96 public totalSupply;

    /// @notice Whether ownership has been transferred to the DAO
    bool public ownershipTransferred;

    /// @notice Address authorized to issue/mint DDX tokens
    address public issuer;

    mapping(address => mapping(address => uint96)) internal allowances;

    mapping(address => uint96) internal balances;

    /// @notice A record of each accounts delegate
    mapping(address => address) public delegates;

    /// @notice A checkpoint for marking vote count from given block
    struct Checkpoint {
        uint32 id;
        uint96 votes;
    }

    /// @notice A record of votes checkpoints for each account, by index
    mapping(address => mapping(uint256 => Checkpoint)) public checkpoints;

    /// @notice The number of checkpoints for each account
    mapping(address => uint256) public numCheckpoints;

    /// @notice A record of states for signing / validating signatures
    mapping(address => uint256) public nonces;

    /// @notice Emitted when an account changes its delegate
    event DelegateChanged(address indexed delegator, address indexed fromDelegate, address indexed toDelegate);

    /// @notice Emitted when a delegate account's vote balance changes
    event DelegateVotesChanged(address indexed delegate, uint96 previousBalance, uint96 newBalance);

    /// @notice Emitted when transfer takes place
    event Transfer(address indexed from, address indexed to, uint256 amount);

    /// @notice Emitted when approval takes place
    event Approval(address indexed owner, address indexed spender, uint256 amount);

    /**
     * @notice Construct a new DDX token
     */
    constructor() public {
        // Set issuer to deploying address
        issuer = msg.sender;

        // Issue pre-mine token supply to deploying address and
        // set the issued and circulating supplies to pre-mine amount
        _transferTokensMint(msg.sender, PRE_MINE_SUPPLY);
    }

    /**
     * @notice Transfer ownership of DDX token from the deploying
     *         address to the DerivaDEX Proxy/DAO
     * @param _derivaDEXProxy DerivaDEX Proxy address
     */
    function transferOwnershipToDerivaDEXProxy(address _derivaDEXProxy) external {
        // Ensure deploying address is calling this, destination is not
        // the zero address, and that ownership has never been
        // transferred thus far
        require(msg.sender == issuer, "DDX: unauthorized transfer of ownership.");
        require(_derivaDEXProxy != address(0), "DDX: transferring to zero address.");
        require(!ownershipTransferred, "DDX: ownership already transferred.");

        // Set ownership transferred boolean flag and the new authorized
        // issuer
        ownershipTransferred = true;
        issuer = _derivaDEXProxy;
    }

    /**
     * @notice Approve `spender` to transfer up to `amount` from `src`
     * @dev This will overwrite the approval amount for `spender`
     *  and is subject to issues noted [here](https://eips.ethereum.org/EIPS/eip-20#approve)
     * @param _spender The address of the account which may transfer tokens
     * @param _amount The number of tokens that are approved (2^256-1 means infinite)
     * @return Whether or not the approval succeeded
     */
    function approve(address _spender, uint256 _amount) external returns (bool) {
        require(_spender != address(0), "DDX: approve to the zero address.");

        // Convert amount to uint96
        uint96 amount;
        if (_amount == uint256(-1)) {
            amount = uint96(-1);
        } else {
            amount = safe96(_amount, "DDX: amount exceeds 96 bits.");
        }

        // Set allowance
        allowances[msg.sender][_spender] = amount;

        emit Approval(msg.sender, _spender, _amount);
        return true;
    }

    /**
     * @dev Atomically increases the allowance granted to `spender` by the caller.
     * This is an alternative to {approve} that can be used as a mitigation for
     * problems described in {IERC20-approve}.
     * Emits an {Approval} event indicating the updated allowance.
     * Requirements:
     * - `spender` cannot be the zero address.
     */
    function increaseAllowance(address _spender, uint256 _addedValue) external returns (bool) {
        require(_spender != address(0), "DDX: approve to the zero address.");

        // Convert amount to uint96
        uint96 amount;
        if (_addedValue == uint256(-1)) {
            amount = uint96(-1);
        } else {
            amount = safe96(_addedValue, "DDX: amount exceeds 96 bits.");
        }

        // Increase allowance
        allowances[msg.sender][_spender] = allowances[msg.sender][_spender].add96(amount);

        emit Approval(msg.sender, _spender, allowances[msg.sender][_spender]);
        return true;
    }

    /**
     * @dev Atomically decreases the allowance granted to `spender` by the caller.
     * This is an alternative to {approve} that can be used as a mitigation for
     * problems described in {IERC20-approve}.
     * Emits an {Approval} event indicating the updated allowance.
     * Requirements:
     * - `spender` cannot be the zero address.
     * - `spender` must have allowance for the caller of at least
     * `subtractedValue`.
     */
    function decreaseAllowance(address _spender, uint256 _subtractedValue) external returns (bool) {
        require(_spender != address(0), "DDX: approve to the zero address.");

        // Convert amount to uint96
        uint96 amount;
        if (_subtractedValue == uint256(-1)) {
            amount = uint96(-1);
        } else {
            amount = safe96(_subtractedValue, "DDX: amount exceeds 96 bits.");
        }

        // Decrease allowance
        allowances[msg.sender][_spender] = allowances[msg.sender][_spender].sub96(
            amount,
            "DDX: decreased allowance below zero."
        );

        emit Approval(msg.sender, _spender, allowances[msg.sender][_spender]);
        return true;
    }

    /**
     * @notice Get the number of tokens held by the `account`
     * @param _account The address of the account to get the balance of
     * @return The number of tokens held
     */
    function balanceOf(address _account) external view returns (uint256) {
        return balances[_account];
    }

    /**
     * @notice Transfer `amount` tokens from `msg.sender` to `dst`
     * @param _recipient The address of the destination account
     * @param _amount The number of tokens to transfer
     * @return Whether or not the transfer succeeded
     */
    function transfer(address _recipient, uint256 _amount) external returns (bool) {
        // Convert amount to uint96
        uint96 amount;
        if (_amount == uint256(-1)) {
            amount = uint96(-1);
        } else {
            amount = safe96(_amount, "DDX: amount exceeds 96 bits.");
        }

        // Transfer tokens from sender to recipient
        _transferTokens(msg.sender, _recipient, amount);
        return true;
    }

    /**
     * @notice Transfer `amount` tokens from `src` to `dst`
     * @param _from The address of the source account
     * @param _recipient The address of the destination account
     * @param _amount The number of tokens to transfer
     * @return Whether or not the transfer succeeded
     */
    function transferFrom(
        address _from,
        address _recipient,
        uint256 _amount
    ) external returns (bool) {
        uint96 spenderAllowance = allowances[_from][msg.sender];

        // Convert amount to uint96
        uint96 amount;
        if (_amount == uint256(-1)) {
            amount = uint96(-1);
        } else {
            amount = safe96(_amount, "DDX: amount exceeds 96 bits.");
        }

        if (msg.sender != _from && spenderAllowance != uint96(-1)) {
            // Tx sender is not the same as transfer sender and doesn't
            // have unlimited allowance.
            // Reduce allowance by amount being transferred
            uint96 newAllowance = spenderAllowance.sub96(amount);
            allowances[_from][msg.sender] = newAllowance;

            emit Approval(_from, msg.sender, newAllowance);
        }

        // Transfer tokens from sender to recipient
        _transferTokens(_from, _recipient, amount);
        return true;
    }

    /**
     * @dev Creates `amount` tokens and assigns them to `account`, increasing
     *      the total supply.
     *
     * Emits a {Transfer} event with `from` set to the zero address.
     *
     * Requirements
     *
     * - `to` cannot be the zero address.
     */
    function mint(address _recipient, uint256 _amount) external {
        require(msg.sender == issuer, "DDX: unauthorized mint.");

        // Convert amount to uint96
        uint96 amount;
        if (_amount == uint256(-1)) {
            amount = uint96(-1);
        } else {
            amount = safe96(_amount, "DDX: amount exceeds 96 bits.");
        }

        // Ensure the mint doesn't cause the issued supply to exceed
        // the total supply that could ever be issued
        require(issuedSupply.add96(amount) <= MAX_SUPPLY, "DDX: cap exceeded.");

        // Mint tokens to recipient
        _transferTokensMint(_recipient, amount);
    }

    /**
     * @dev Creates `amount` tokens and assigns them to `account`, decreasing
     *      the total supply.
     *
     * Emits a {Transfer} event with `from` set to the zero address.
     *
     * Requirements
     *
     * - `to` cannot be the zero address.
     */
    function burn(uint256 _amount) external {
        // Convert amount to uint96
        uint96 amount;
        if (_amount == uint256(-1)) {
            amount = uint96(-1);
        } else {
            amount = safe96(_amount, "DDX: amount exceeds 96 bits.");
        }

        // Burn tokens from sender
        _transferTokensBurn(msg.sender, amount);
    }

    /**
     * @dev Creates `amount` tokens and assigns them to `account`, increasing
     *      the total supply.
     *
     * Emits a {Transfer} event with `from` set to the zero address.
     *
     * Requirements
     *
     * - `to` cannot be the zero address.
     */
    function burnFrom(address _account, uint256 _amount) external {
        uint96 spenderAllowance = allowances[_account][msg.sender];

        // Convert amount to uint96
        uint96 amount;
        if (_amount == uint256(-1)) {
            amount = uint96(-1);
        } else {
            amount = safe96(_amount, "DDX: amount exceeds 96 bits.");
        }

        if (msg.sender != _account && spenderAllowance != uint96(-1)) {
            // Tx sender is not the same as burn account and doesn't
            // have unlimited allowance.
            // Reduce allowance by amount being transferred
            uint96 newAllowance = spenderAllowance.sub96(amount, "DDX: burn amount exceeds allowance.");
            allowances[_account][msg.sender] = newAllowance;

            emit Approval(_account, msg.sender, newAllowance);
        }

        // Burn tokens from account
        _transferTokensBurn(_account, amount);
    }

    /**
     * @notice Delegate votes from `msg.sender` to `delegatee`
     * @param _delegatee The address to delegate votes to
     */
    function delegate(address _delegatee) external {
        _delegate(msg.sender, _delegatee);
    }

    /**
     * @notice Delegates votes from signatory to `delegatee`
     * @param _delegatee The address to delegate votes to
     * @param _nonce The contract state required to match the signature
     * @param _expiry The time at which to expire the signature
     * @param _signature Signature
     */
    function delegateBySig(
        address _delegatee,
        uint256 _nonce,
        uint256 _expiry,
        bytes memory _signature
    ) external {
        // Perform EIP712 hashing logic
        bytes32 eip712OrderParamsDomainHash = LibEIP712.hashEIP712Domain(name, version, getChainId(), address(this));
        bytes32 delegationHash =
            LibDelegation.getDelegationHash(
                LibDelegation.Delegation({ delegatee: _delegatee, nonce: _nonce, expiry: _expiry }),
                eip712OrderParamsDomainHash
            );

        // Perform sig recovery
        uint8 v = uint8(_signature[0]);
        bytes32 r = _signature.readBytes32(1);
        bytes32 s = _signature.readBytes32(33);
        address recovered = ecrecover(delegationHash, v, r, s);

        require(recovered != address(0), "DDX: invalid signature.");
        require(_nonce == nonces[recovered]++, "DDX: invalid nonce.");
        require(block.timestamp <= _expiry, "DDX: signature expired.");

        // Delegate votes from recovered address to delegatee
        _delegate(recovered, _delegatee);
    }

    /**
     * @notice Permits allowance from signatory to `spender`
     * @param _spender The spender being approved
     * @param _value The value being approved
     * @param _nonce The contract state required to match the signature
     * @param _expiry The time at which to expire the signature
     * @param _signature Signature
     */
    function permit(
        address _spender,
        uint256 _value,
        uint256 _nonce,
        uint256 _expiry,
        bytes memory _signature
    ) external {
        // Perform EIP712 hashing logic
        bytes32 eip712OrderParamsDomainHash = LibEIP712.hashEIP712Domain(name, version, getChainId(), address(this));
        bytes32 permitHash =
            LibPermit.getPermitHash(
                LibPermit.Permit({ spender: _spender, value: _value, nonce: _nonce, expiry: _expiry }),
                eip712OrderParamsDomainHash
            );

        // Perform sig recovery
        uint8 v = uint8(_signature[0]);
        bytes32 r = _signature.readBytes32(1);
        bytes32 s = _signature.readBytes32(33);

        // EIP-2 still allows signature malleability for ecrecover(). Remove this possibility and make the signature
        // unique. Appendix F in the Ethereum Yellow paper (https://ethereum.github.io/yellowpaper/paper.pdf), defines
        // the valid range for s in (281): 0 < s < secp256k1n ÷ 2 + 1, and for v in (282): v ∈ {27, 28}. Most
        // signatures from current libraries generate a unique signature with an s-value in the lower half order.
        //
        // If your library generates malleable signatures, such as s-values in the upper range, calculate a new s-value
        // with 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141 - s1 and flip v from 27 to 28 or
        // vice versa. If your library also generates signatures with 0/1 for v instead 27/28, add 27 to v to accept
        // these malleable signatures as well.
        if (uint256(s) > 0x7FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF5D576E7357A4501DDFE92F46681B20A0) {
            revert("ECDSA: invalid signature 's' value");
        }

        if (v != 27 && v != 28) {
            revert("ECDSA: invalid signature 'v' value");
        }

        address recovered = ecrecover(permitHash, v, r, s);

        require(recovered != address(0), "DDX: invalid signature.");
        require(_nonce == nonces[recovered]++, "DDX: invalid nonce.");
        require(block.timestamp <= _expiry, "DDX: signature expired.");

        // Convert amount to uint96
        uint96 amount;
        if (_value == uint256(-1)) {
            amount = uint96(-1);
        } else {
            amount = safe96(_value, "DDX: amount exceeds 96 bits.");
        }

        // Set allowance
        allowances[recovered][_spender] = amount;
        emit Approval(recovered, _spender, _value);
    }

    /**
     * @notice Get the number of tokens `spender` is approved to spend on behalf of `account`
     * @param _account The address of the account holding the funds
     * @param _spender The address of the account spending the funds
     * @return The number of tokens approved
     */
    function allowance(address _account, address _spender) external view returns (uint256) {
        return allowances[_account][_spender];
    }

    /**
     * @notice Gets the current votes balance.
     * @param _account The address to get votes balance.
     * @return The number of current votes.
     */
    function getCurrentVotes(address _account) external view returns (uint96) {
        uint256 numCheckpointsAccount = numCheckpoints[_account];
        return numCheckpointsAccount > 0 ? checkpoints[_account][numCheckpointsAccount - 1].votes : 0;
    }

    /**
     * @notice Determine the prior number of votes for an account as of a block number
     * @dev Block number must be a finalized block or else this function will revert to prevent misinformation.
     * @param _account The address of the account to check
     * @param _blockNumber The block number to get the vote balance at
     * @return The number of votes the account had as of the given block
     */
    function getPriorVotes(address _account, uint256 _blockNumber) external view returns (uint96) {
        require(_blockNumber < block.number, "DDX: block not yet determined.");

        uint256 numCheckpointsAccount = numCheckpoints[_account];
        if (numCheckpointsAccount == 0) {
            return 0;
        }

        // First check most recent balance
        if (checkpoints[_account][numCheckpointsAccount - 1].id <= _blockNumber) {
            return checkpoints[_account][numCheckpointsAccount - 1].votes;
        }

        // Next check implicit zero balance
        if (checkpoints[_account][0].id > _blockNumber) {
            return 0;
        }

        // Perform binary search to find the most recent token holdings
        // leading to a measure of voting power
        uint256 lower = 0;
        uint256 upper = numCheckpointsAccount - 1;
        while (upper > lower) {
            // ceil, avoiding overflow
            uint256 center = upper - (upper - lower) / 2;
            Checkpoint memory cp = checkpoints[_account][center];
            if (cp.id == _blockNumber) {
                return cp.votes;
            } else if (cp.id < _blockNumber) {
                lower = center;
            } else {
                upper = center - 1;
            }
        }
        return checkpoints[_account][lower].votes;
    }

    function _delegate(address _delegator, address _delegatee) internal {
        // Get the current address delegator has delegated
        address currentDelegate = _getDelegatee(_delegator);

        // Get delegator's DDX balance
        uint96 delegatorBalance = balances[_delegator];

        // Set delegator's new delegatee address
        delegates[_delegator] = _delegatee;

        emit DelegateChanged(_delegator, currentDelegate, _delegatee);

        // Move votes from currently-delegated address to
        // new address
        _moveDelegates(currentDelegate, _delegatee, delegatorBalance);
    }

    function _transferTokens(
        address _spender,
        address _recipient,
        uint96 _amount
    ) internal {
        require(_spender != address(0), "DDX: cannot transfer from the zero address.");
        require(_recipient != address(0), "DDX: cannot transfer to the zero address.");

        // Reduce spender's balance and increase recipient balance
        balances[_spender] = balances[_spender].sub96(_amount);
        balances[_recipient] = balances[_recipient].add96(_amount);
        emit Transfer(_spender, _recipient, _amount);

        // Move votes from currently-delegated address to
        // recipient's delegated address
        _moveDelegates(_getDelegatee(_spender), _getDelegatee(_recipient), _amount);
    }

    function _transferTokensMint(address _recipient, uint96 _amount) internal {
        require(_recipient != address(0), "DDX: cannot transfer to the zero address.");

        // Add to recipient's balance
        balances[_recipient] = balances[_recipient].add96(_amount);

        // Increase the issued supply and circulating supply
        issuedSupply = issuedSupply.add96(_amount);
        totalSupply = totalSupply.add96(_amount);

        emit Transfer(address(0), _recipient, _amount);

        // Add delegates to recipient's delegated address
        _moveDelegates(address(0), _getDelegatee(_recipient), _amount);
    }

    function _transferTokensBurn(address _spender, uint96 _amount) internal {
        require(_spender != address(0), "DDX: cannot transfer from the zero address.");

        // Reduce the spender/burner's balance
        balances[_spender] = balances[_spender].sub96(_amount, "DDX: not enough balance to burn.");

        // Reduce the total supply
        totalSupply = totalSupply.sub96(_amount);
        emit Transfer(_spender, address(0), _amount);

        // MRedduce delegates from spender's delegated address
        _moveDelegates(_getDelegatee(_spender), address(0), _amount);
    }

    function _moveDelegates(
        address _initDel,
        address _finDel,
        uint96 _amount
    ) internal {
        if (_initDel != _finDel && _amount > 0) {
            // Initial delegated address is different than final
            // delegated address and nonzero number of votes moved
            if (_initDel != address(0)) {
                uint256 initDelNum = numCheckpoints[_initDel];

                // Retrieve and compute the old and new initial delegate
                // address' votes
                uint96 initDelOld = initDelNum > 0 ? checkpoints[_initDel][initDelNum - 1].votes : 0;
                uint96 initDelNew = initDelOld.sub96(_amount);
                _writeCheckpoint(_initDel, initDelOld, initDelNew);
            }

            if (_finDel != address(0)) {
                uint256 finDelNum = numCheckpoints[_finDel];

                // Retrieve and compute the old and new final delegate
                // address' votes
                uint96 finDelOld = finDelNum > 0 ? checkpoints[_finDel][finDelNum - 1].votes : 0;
                uint96 finDelNew = finDelOld.add96(_amount);
                _writeCheckpoint(_finDel, finDelOld, finDelNew);
            }
        }
    }

    function _writeCheckpoint(
        address _delegatee,
        uint96 _oldVotes,
        uint96 _newVotes
    ) internal {
        uint32 blockNumber = safe32(block.number, "DDX: exceeds 32 bits.");
        uint256 delNum = numCheckpoints[_delegatee];
        if (delNum > 0 && checkpoints[_delegatee][delNum - 1].id == blockNumber) {
            // If latest checkpoint is current block, edit in place
            checkpoints[_delegatee][delNum - 1].votes = _newVotes;
        } else {
            // Create a new id, vote pair
            checkpoints[_delegatee][delNum] = Checkpoint({ id: blockNumber, votes: _newVotes });
            numCheckpoints[_delegatee] = delNum.add(1);
        }

        emit DelegateVotesChanged(_delegatee, _oldVotes, _newVotes);
    }

    function _getDelegatee(address _delegator) internal view returns (address) {
        if (delegates[_delegator] == address(0)) {
            return _delegator;
        }
        return delegates[_delegator];
    }

    function safe32(uint256 n, string memory errorMessage) internal pure returns (uint32) {
        require(n < 2**32, errorMessage);
        return uint32(n);
    }

    function safe96(uint256 n, string memory errorMessage) internal pure returns (uint96) {
        require(n < 2**96, errorMessage);
        return uint96(n);
    }

    function getChainId() internal pure returns (uint256) {
        uint256 chainId;
        assembly {
            chainId := chainid()
        }
        return chainId;
    }
}

// SPDX-License-Identifier: MIT
pragma solidity 0.6.12;
pragma experimental ABIEncoderV2;

import { Context } from "openzeppelin-solidity/contracts/GSN/Context.sol";
import { IERC20 } from "openzeppelin-solidity/contracts/token/ERC20/IERC20.sol";
import { SafeERC20 } from "openzeppelin-solidity/contracts/token/ERC20/SafeERC20.sol";

contract SafeERC20Wrapper is Context {
    using SafeERC20 for IERC20;

    IERC20 private _token;

    constructor(IERC20 token) public {
        _token = token;
    }

    function transfer(address recipient, uint256 amount) public {
        _token.safeTransfer(recipient, amount);
    }

    function transferFrom(
        address sender,
        address recipient,
        uint256 amount
    ) public {
        _token.safeTransferFrom(sender, recipient, amount);
    }

    function approve(address spender, uint256 amount) public {
        _token.safeApprove(spender, amount);
    }

    function increaseAllowance(address spender, uint256 amount) public {
        _token.safeIncreaseAllowance(spender, amount);
    }

    function decreaseAllowance(address spender, uint256 amount) public {
        _token.safeDecreaseAllowance(spender, amount);
    }

    function allowance(address owner, address spender) public view returns (uint256) {
        return _token.allowance(owner, spender);
    }

    function balanceOf(address account) public view returns (uint256) {
        return _token.balanceOf(account);
    }
}




// SPDX-License-Identifier: MIT

pragma solidity ^0.6.0;

import "../../GSN/Context.sol";
import "./IERC20.sol";
import "../../math/SafeMath.sol"; kevin
import "../../utils/Address.sol"; kevin

/**
 * @dev Implementation of the {IERC20} interface.
 *
 * This implementation is agnostic to the way tokens are created. This means
 * that a supply mechanism has to be added in a derived contract using {_mint}.
 * For a generic mechanism see {ERC20PresetMinterPauser}.
 *
 * TIP: For a detailed writeup see our guide
 * https://forum.zeppelin.solutions/t/how-to-implement-erc20-supply-mechanisms/226[How
 * to implement supply mechanisms].
 *
 * We have followed general OpenZeppelin guidelines: functions revert instead
 * of returning `false` on failure. This behavior is nonetheless conventional
 * and does not conflict with the expectations of ERC20 applications.
 *
 * Additionally, an {Approval} event is emitted on calls to {transferFrom}.
 * This allows applications to reconstruct the allowance for all accounts just
 * by listening to said events. Other implementations of the EIP may not emit
 * these events, as it isn't required by the specification.
 *
 * Finally, the non-standard {decreaseAllowance} and {increaseAllowance}
 * functions have been added to mitigate the well-known issues around setting
 * allowances. See {IERC20-approve}.
 */
contract ERC20 is Context, IERC20 {
    using SafeMath for uint256;
    using Address for address;

    mapping (address => uint256) private _balances;

    mapping (address => mapping (address => uint256)) private _allowances;

    uint256 private _totalSupply;

    string private _name;
    string private _symbol;
    uint8 private _decimals;

    /**
     * @dev Sets the values for {name} and {symbol}, initializes {decimals} with
     * a default value of 18.
     *
     * To select a different value for {decimals}, use {_setupDecimals}.
     *
     * All three of these values are immutable: they can only be set once during
     * construction.
     */
    constructor (string memory name, string memory symbol) public {
        _name = name;
        _symbol = symbol;
        _decimals = 18;
    }

    /**
     * @dev Returns the name of the token.
     */
    function name() public view returns (string memory) {
        return _name;
    }

    /**
     * @dev Returns the symbol of the token, usually a shorter version of the
     * name.
     */
    function symbol() public view returns (string memory) {
        return _symbol;
    }

    /**
     * @dev Returns the number of decimals used to get its user representation.
     * For example, if `decimals` equals `2`, a balance of `505` tokens should
     * be displayed to a user as `5,05` (`505 / 10 ** 2`).
     *
     * Tokens usually opt for a value of 18, imitating the relationship between
     * Ether and Wei. This is the value {ERC20} uses, unless {_setupDecimals} is
     * called.
     *
     * NOTE: This information is only used for _display_ purposes: it in
     * no way affects any of the arithmetic of the contract, including
     * {IERC20-balanceOf} and {IERC20-transfer}.
     */
    function decimals() public view returns (uint8) {
        return _decimals;
    }

    /**
     * @dev See {IERC20-totalSupply}.
     */
    function totalSupply() public view override returns (uint256) {
        return _totalSupply;
    }

    /**
     * @dev See {IERC20-balanceOf}.
     */
    function balanceOf(address account) public view override returns (uint256) {
        return _balances[account];
    }

    /**
     * @dev See {IERC20-transfer}.
     *
     * Requirements:
     *
     * - `recipient` cannot be the zero address.
     * - the caller must have a balance of at least `amount`.
     */
    function transfer(address recipient, uint256 amount) public virtual override returns (bool) {
        _transfer(_msgSender(), recipient, amount);
        return true;
    }

    /**
     * @dev See {IERC20-allowance}.
     */
    function allowance(address owner, address spender) public view virtual override returns (uint256) {
        return _allowances[owner][spender];
    }

    /**
     * @dev See {IERC20-approve}.
     *
     * Requirements:
     *
     * - `spender` cannot be the zero address.
     */
    function approve(address spender, uint256 amount) public virtual override returns (bool) {
        _approve(_msgSender(), spender, amount);
        return true;
    }

    /**
     * @dev See {IERC20-transferFrom}.
     *
     * Emits an {Approval} event indicating the updated allowance. This is not
     * required by the EIP. See the note at the beginning of {ERC20};
     *
     * Requirements:
     * - `sender` and `recipient` cannot be the zero address.
     * - `sender` must have a balance of at least `amount`.
     * - the caller must have allowance for ``sender``'s tokens of at least
     * `amount`.
     */
    function transferFrom(address sender, address recipient, uint256 amount) public virtual override returns (bool) {
        _transfer(sender, recipient, amount);
        _approve(sender, _msgSender(), _allowances[sender][_msgSender()].sub(amount, "ERC20: transfer amount exceeds allowance"));
        return true;
    }

    /**
     * @dev Atomically increases the allowance granted to `spender` by the caller.
     *
     * This is an alternative to {approve} that can be used as a mitigation for
     * problems described in {IERC20-approve}.
     *
     * Emits an {Approval} event indicating the updated allowance.
     *
     * Requirements:
     *
     * - `spender` cannot be the zero address.
     */
    function increaseAllowance(address spender, uint256 addedValue) public virtual returns (bool) {
        _approve(_msgSender(), spender, _allowances[_msgSender()][spender].add(addedValue));
        return true;
    }

    /**
     * @dev Atomically decreases the allowance granted to `spender` by the caller.
     *
     * This is an alternative to {approve} that can be used as a mitigation for
     * problems described in {IERC20-approve}.
     *
     * Emits an {Approval} event indicating the updated allowance.
     *
     * Requirements:
     *
     * - `spender` cannot be the zero address.
     * - `spender` must have allowance for the caller of at least
     * `subtractedValue`.
     */
    function decreaseAllowance(address spender, uint256 subtractedValue) public virtual returns (bool) {
        _approve(_msgSender(), spender, _allowances[_msgSender()][spender].sub(subtractedValue, "ERC20: decreased allowance below zero"));
        return true;
    }

    /**
     * @dev Moves tokens `amount` from `sender` to `recipient`.
     *
     * This is internal function is equivalent to {transfer}, and can be used to
     * e.g. implement automatic token fees, slashing mechanisms, etc.
     *
     * Emits a {Transfer} event.
     *
     * Requirements:
     *
     * - `sender` cannot be the zero address.
     * - `recipient` cannot be the zero address.
     * - `sender` must have a balance of at least `amount`.
     */
    function _transfer(address sender, address recipient, uint256 amount) internal virtual {
        require(sender != address(0), "ERC20: transfer from the zero address");
        require(recipient != address(0), "ERC20: transfer to the zero address");

        _beforeTokenTransfer(sender, recipient, amount);

        _balances[sender] = _balances[sender].sub(amount, "ERC20: transfer amount exceeds balance");
        _balances[recipient] = _balances[recipient].add(amount);
        emit Transfer(sender, recipient, amount);
    }

    /** @dev Creates `amount` tokens and assigns them to `account`, increasing
     * the total supply.
     *
     * Emits a {Transfer} event with `from` set to the zero address.
     *
     * Requirements
     *
     * - `to` cannot be the zero address.
     */
    function _mint(address account, uint256 amount) internal virtual {
        require(account != address(0), "ERC20: mint to the zero address");

        _beforeTokenTransfer(address(0), account, amount);

        _totalSupply = _totalSupply.add(amount);
        _balances[account] = _balances[account].add(amount);
        emit Transfer(address(0), account, amount);
    }

    /**
     * @dev Destroys `amount` tokens from `account`, reducing the
     * total supply.
     *
     * Emits a {Transfer} event with `to` set to the zero address.
     *
     * Requirements
     *
     * - `account` cannot be the zero address.
     * - `account` must have at least `amount` tokens.
     */
    function _burn(address account, uint256 amount) internal virtual {
        require(account != address(0), "ERC20: burn from the zero address");

        _beforeTokenTransfer(account, address(0), amount);

        _balances[account] = _balances[account].sub(amount, "ERC20: burn amount exceeds balance");
        _totalSupply = _totalSupply.sub(amount);
        emit Transfer(account, address(0), amount);
    }

    /**
     * @dev Sets `amount` as the allowance of `spender` over the `owner` s tokens.
     *
     * This internal function is equivalent to `approve`, and can be used to
     * e.g. set automatic allowances for certain subsystems, etc.
     *
     * Emits an {Approval} event.
     *
     * Requirements:
     *
     * - `owner` cannot be the zero address.
     * - `spender` cannot be the zero address.
     */
    function _approve(address owner, address spender, uint256 amount) internal virtual {
        require(owner != address(0), "ERC20: approve from the zero address");
        require(spender != address(0), "ERC20: approve to the zero address");

        _allowances[owner][spender] = amount;
        emit Approval(owner, spender, amount);
    }

    /**
     * @dev Sets {decimals} to a value other than the default one of 18.
     *
     * WARNING: This function should only be called from the constructor. Most
     * applications that interact with token contracts will not expect
     * {decimals} to ever change, and may work incorrectly if it does.
     */
    function _setupDecimals(uint8 decimals_) internal {
        _decimals = decimals_;
    }

    /**
     * @dev Hook that is called before any transfer of tokens. This includes
     * minting and burning.
     *
     * Calling conditions:
     *
     * - when `from` and `to` are both non-zero, `amount` of ``from``'s tokens
     * will be to transferred to `to`.
     * - when `from` is zero, `amount` tokens will be minted for `to`.
     * - when `to` is zero, `amount` of ``from``'s tokens will be burned.
     * - `from` and `to` are never both zero.
     *
     * To learn more about hooks, head to xref:ROOT:extending-contracts.adoc#using-hooks[Using Hooks].
     */
    function _beforeTokenTransfer(address from, address to, uint256 amount) internal virtual { }
}




// SPDX-License-Identifier: MIT
pragma solidity 0.6.12;

import "openzeppelin-solidity/contracts/token/ERC20/ERC20.sol";

// mock class using ERC20
contract DummyToken is ERC20 {
    uint256 public constant INITIAL_SUPPLY = 100000000 * (10**18);

    constructor(string memory name, string memory symbol) public payable ERC20(name, symbol) {
        _mint(msg.sender, INITIAL_SUPPLY);
    }

    function mint(address account, uint256 amount) public {
        _mint(account, amount);
    }

    function burn(address account, uint256 amount) public {
        _burn(account, amount);
    }

    function transferInternal(
        address from,
        address to,
        uint256 value
    ) public {
        _transfer(from, to, value);
    }

    function approveInternal(
        address owner,
        address spender,
        uint256 value
    ) public {
        _approve(owner, spender, value);
    }
}

// SPDX-License-Identifier: MIT
pragma solidity 0.6.12;
pragma experimental ABIEncoderV2;

/******************************************************************************\
* Author: Nick Mudge <nick@perfectabstractions.com> (https://twitter.com/mudgen)
*
* Implementation of internal diamondCut function.
/******************************************************************************/

import "./LibDiamondStorage.sol";
import "./IDiamondCut.sol";

library LibDiamondCut {
    event DiamondCut(IDiamondCut.FacetCut[] _diamondCut, address _init, bytes _calldata);

    // Internal function version of diamondCut
    // This code is almost the same as the external diamondCut,
    // except it is using 'FacetCut[] memory _diamondCut' instead of
    // 'FacetCut[] calldata _diamondCut'.
    // The code is duplicated to prevent copying calldata to memory which
    // causes an error for a two dimensional array.
    function diamondCut(
        IDiamondCut.FacetCut[] memory _diamondCut,
        address _init,
        bytes memory _calldata
    ) internal {
        require(_diamondCut.length > 0, "LibDiamondCut: No facets to cut");
        for (uint256 facetIndex; facetIndex < _diamondCut.length; facetIndex++) {
            addReplaceRemoveFacetSelectors(
                _diamondCut[facetIndex].facetAddress,
                _diamondCut[facetIndex].action,
                _diamondCut[facetIndex].functionSelectors
            );
        }
        emit DiamondCut(_diamondCut, _init, _calldata);
        initializeDiamondCut(_init, _calldata);
    }

    function addReplaceRemoveFacetSelectors(
        address _newFacetAddress,
        IDiamondCut.FacetCutAction _action,
        bytes4[] memory _selectors
    ) internal {
        LibDiamondStorage.DiamondStorage storage ds = LibDiamondStorage.diamondStorage();
        require(_selectors.length > 0, "LibDiamondCut: No selectors in facet to cut");
        // add or replace functions
        if (_newFacetAddress != address(0)) {
            uint256 facetAddressPosition = ds.facetFunctionSelectors[_newFacetAddress].facetAddressPosition;
            // add new facet address if it does not exist
            if (
                facetAddressPosition == 0 && ds.facetFunctionSelectors[_newFacetAddress].functionSelectors.length == 0
            ) {
                ensureHasContractCode(_newFacetAddress, "LibDiamondCut: New facet has no code");
                facetAddressPosition = ds.facetAddresses.length;
                ds.facetAddresses.push(_newFacetAddress);
                ds.facetFunctionSelectors[_newFacetAddress].facetAddressPosition = uint16(facetAddressPosition);
            }
            // add or replace selectors
            for (uint256 selectorIndex; selectorIndex < _selectors.length; selectorIndex++) {
                bytes4 selector = _selectors[selectorIndex];
                address oldFacetAddress = ds.selectorToFacetAndPosition[selector].facetAddress;
                // add
                if (_action == IDiamondCut.FacetCutAction.Add) {
                    require(oldFacetAddress == address(0), "LibDiamondCut: Can't add function that already exists");
                    addSelector(_newFacetAddress, selector);
                } else if (_action == IDiamondCut.FacetCutAction.Replace) {
                    // replace
                    require(
                        oldFacetAddress != _newFacetAddress,
                        "LibDiamondCut: Can't replace function with same function"
                    );
                    removeSelector(oldFacetAddress, selector);
                    addSelector(_newFacetAddress, selector);
                } else {
                    revert("LibDiamondCut: Incorrect FacetCutAction");
                }
            }
        } else {
            require(
                _action == IDiamondCut.FacetCutAction.Remove,
                "LibDiamondCut: action not set to FacetCutAction.Remove"
            );
            // remove selectors
            for (uint256 selectorIndex; selectorIndex < _selectors.length; selectorIndex++) {
                bytes4 selector = _selectors[selectorIndex];
                removeSelector(ds.selectorToFacetAndPosition[selector].facetAddress, selector);
            }
        }
    }

    function addSelector(address _newFacet, bytes4 _selector) internal {
        LibDiamondStorage.DiamondStorage storage ds = LibDiamondStorage.diamondStorage();
        uint256 selectorPosition = ds.facetFunctionSelectors[_newFacet].functionSelectors.length;
        ds.facetFunctionSelectors[_newFacet].functionSelectors.push(_selector);
        ds.selectorToFacetAndPosition[_selector].facetAddress = _newFacet;
        ds.selectorToFacetAndPosition[_selector].functionSelectorPosition = uint16(selectorPosition);
    }

    function removeSelector(address _oldFacetAddress, bytes4 _selector) internal {
        LibDiamondStorage.DiamondStorage storage ds = LibDiamondStorage.diamondStorage();
        require(_oldFacetAddress != address(0), "LibDiamondCut: Can't remove or replace function that doesn't exist");
        // replace selector with last selector, then delete last selector
        uint256 selectorPosition = ds.selectorToFacetAndPosition[_selector].functionSelectorPosition;
        uint256 lastSelectorPosition = ds.facetFunctionSelectors[_oldFacetAddress].functionSelectors.length - 1;
        bytes4 lastSelector = ds.facetFunctionSelectors[_oldFacetAddress].functionSelectors[lastSelectorPosition];
        // if not the same then replace _selector with lastSelector
        if (lastSelector != _selector) {
            ds.facetFunctionSelectors[_oldFacetAddress].functionSelectors[selectorPosition] = lastSelector;
            ds.selectorToFacetAndPosition[lastSelector].functionSelectorPosition = uint16(selectorPosition);
        }
        // delete the last selector
        ds.facetFunctionSelectors[_oldFacetAddress].functionSelectors.pop();
        delete ds.selectorToFacetAndPosition[_selector];

        // if no more selectors for facet address then delete the facet address
        if (lastSelectorPosition == 0) {
            // replace facet address with last facet address and delete last facet address
            uint256 lastFacetAddressPosition = ds.facetAddresses.length - 1;
            address lastFacetAddress = ds.facetAddresses[lastFacetAddressPosition];
            uint256 facetAddressPosition = ds.facetFunctionSelectors[_oldFacetAddress].facetAddressPosition;
            if (_oldFacetAddress != lastFacetAddress) {
                ds.facetAddresses[facetAddressPosition] = lastFacetAddress;
                ds.facetFunctionSelectors[lastFacetAddress].facetAddressPosition = uint16(facetAddressPosition);
            }
            ds.facetAddresses.pop();
            delete ds.facetFunctionSelectors[_oldFacetAddress];
        }
    }

    function initializeDiamondCut(address _init, bytes memory _calldata) internal {
        if (_init == address(0)) {
            require(_calldata.length == 0, "LibDiamondCut: _init is address(0) but_calldata is not empty");
        } else {
            require(_calldata.length > 0, "LibDiamondCut: _calldata is empty but _init is not address(0)");
            if (_init != address(this)) {
                LibDiamondCut.ensureHasContractCode(_init, "LibDiamondCut: _init address has no code");
            }
            (bool success, bytes memory error) = _init.delegatecall(_calldata);
            if (!success) {
                if (error.length > 0) {
                    // bubble up the error
                    revert(string(error));
                } else {
                    revert("LibDiamondCut: _init function reverted");
                }
            }
        }
    }

    function ensureHasContractCode(address _contract, string memory _errorMessage) internal view {
        uint256 contractSize;
        assembly {
            contractSize := extcodesize(_contract)
        }
        require(contractSize > 0, _errorMessage);
    }
}







// SPDX-License-Identifier: MIT
pragma solidity 0.6.12;
pragma experimental ABIEncoderV2;

/******************************************************************************\
* Author: Nick Mudge <nick@perfectabstractions.com> (https://twitter.com/mudgen)
*
* Implementation of diamondCut external function and DiamondLoupe interface.
/******************************************************************************/

import "./LibDiamondStorage.sol";
import "./LibDiamondCut.sol";
import "../storage/LibDiamondStorageDerivaDEX.sol";
import "./IDiamondCut.sol";
import "./IDiamondLoupe.sol";
import "./IERC165.sol";

contract DiamondFacet is IDiamondCut, IDiamondLoupe, IERC165 {
    // Standard diamondCut external function
    /// @notice Add/replace/remove any number of functions and optionally execute
    ///         a function with delegatecall
    /// @param _diamondCut Contains the facet addresses and function selectors
    /// @param _init The address of the contract or facet to execute _calldata
    /// @param _calldata A function call, including function selector and arguments
    ///                  _calldata is executed with delegatecall on _init
    function diamondCut(
        FacetCut[] calldata _diamondCut,
        address _init,
        bytes calldata _calldata
    ) external override {
        LibDiamondStorageDerivaDEX.DiamondStorageDerivaDEX storage dsDerivaDEX =
            LibDiamondStorageDerivaDEX.diamondStorageDerivaDEX();
        require(msg.sender == dsDerivaDEX.admin, "DiamondFacet: Must own the contract");
        require(_diamondCut.length > 0, "DiamondFacet: No facets to cut");
        for (uint256 facetIndex; facetIndex < _diamondCut.length; facetIndex++) {
            LibDiamondCut.addReplaceRemoveFacetSelectors(
                _diamondCut[facetIndex].facetAddress,
                _diamondCut[facetIndex].action,
                _diamondCut[facetIndex].functionSelectors
            );
        }
        emit DiamondCut(_diamondCut, _init, _calldata);
        LibDiamondCut.initializeDiamondCut(_init, _calldata);
    }

    // Diamond Loupe Functions
    ////////////////////////////////////////////////////////////////////
    /// These functions are expected to be called frequently by tools.
    //
    // struct Facet {
    //     address facetAddress;
    //     bytes4[] functionSelectors;
    // }
    //
    /// @notice Gets all facets and their selectors.
    /// @return facets_ Facet
    function facets() external view override returns (Facet[] memory facets_) {
        LibDiamondStorage.DiamondStorage storage ds = LibDiamondStorage.diamondStorage();
        uint256 numFacets = ds.facetAddresses.length;
        facets_ = new Facet[](numFacets);
        for (uint256 i; i < numFacets; i++) {
            address facetAddress_ = ds.facetAddresses[i];
            facets_[i].facetAddress = facetAddress_;
            facets_[i].functionSelectors = ds.facetFunctionSelectors[facetAddress_].functionSelectors;
        }
    }

    /// @notice Gets all the function selectors provided by a facet.
    /// @param _facet The facet address.
    /// @return facetFunctionSelectors_
    function facetFunctionSelectors(address _facet)
        external
        view
        override
        returns (bytes4[] memory facetFunctionSelectors_)
    {
        LibDiamondStorage.DiamondStorage storage ds = LibDiamondStorage.diamondStorage();
        facetFunctionSelectors_ = ds.facetFunctionSelectors[_facet].functionSelectors;
    }

    /// @notice Get all the facet addresses used by a diamond.
    /// @return facetAddresses_
    function facetAddresses() external view override returns (address[] memory facetAddresses_) {
        LibDiamondStorage.DiamondStorage storage ds = LibDiamondStorage.diamondStorage();
        facetAddresses_ = ds.facetAddresses;
    }

    /// @notice Gets the facet that supports the given selector.
    /// @dev If facet is not found return address(0).
    /// @param _functionSelector The function selector.
    /// @return facetAddress_ The facet address.
    function facetAddress(bytes4 _functionSelector) external view override returns (address facetAddress_) {
        LibDiamondStorage.DiamondStorage storage ds = LibDiamondStorage.diamondStorage();
        facetAddress_ = ds.selectorToFacetAndPosition[_functionSelector].facetAddress;
    }

    // This implements ERC-165.
    function supportsInterface(bytes4 _interfaceId) external view override returns (bool) {
        LibDiamondStorage.DiamondStorage storage ds = LibDiamondStorage.diamondStorage();
        return ds.supportedInterfaces[_interfaceId];
    }
}




// SPDX-License-Identifier: MIT
pragma solidity 0.6.12;
pragma experimental ABIEncoderV2;

/******************************************************************************\
* Author: Nick Mudge <nick@perfectabstractions.com> (https://twitter.com/mudgen)
*
* Implementation of internal diamondCut function.
/******************************************************************************/

import "./LibDiamondStorage.sol";
import "./IDiamondCut.sol";

library LibDiamondCut {
    event DiamondCut(IDiamondCut.FacetCut[] _diamondCut, address _init, bytes _calldata);

    // Internal function version of diamondCut
    // This code is almost the same as the external diamondCut,
    // except it is using 'FacetCut[] memory _diamondCut' instead of
    // 'FacetCut[] calldata _diamondCut'.
    // The code is duplicated to prevent copying calldata to memory which
    // causes an error for a two dimensional array.
    function diamondCut(
        IDiamondCut.FacetCut[] memory _diamondCut,
        address _init,
        bytes memory _calldata
    ) internal {
        require(_diamondCut.length > 0, "LibDiamondCut: No facets to cut");
        for (uint256 facetIndex; facetIndex < _diamondCut.length; facetIndex++) {
            addReplaceRemoveFacetSelectors(
                _diamondCut[facetIndex].facetAddress,
                _diamondCut[facetIndex].action,
                _diamondCut[facetIndex].functionSelectors
            );
        }
        emit DiamondCut(_diamondCut, _init, _calldata);
        initializeDiamondCut(_init, _calldata);
    }

    function addReplaceRemoveFacetSelectors(
        address _newFacetAddress,
        IDiamondCut.FacetCutAction _action,
        bytes4[] memory _selectors
    ) internal {
        LibDiamondStorage.DiamondStorage storage ds = LibDiamondStorage.diamondStorage();
        require(_selectors.length > 0, "LibDiamondCut: No selectors in facet to cut");
        // add or replace functions
        if (_newFacetAddress != address(0)) {
            uint256 facetAddressPosition = ds.facetFunctionSelectors[_newFacetAddress].facetAddressPosition;
            // add new facet address if it does not exist
            if (
                facetAddressPosition == 0 && ds.facetFunctionSelectors[_newFacetAddress].functionSelectors.length == 0
            ) {
                ensureHasContractCode(_newFacetAddress, "LibDiamondCut: New facet has no code");
                facetAddressPosition = ds.facetAddresses.length;
                ds.facetAddresses.push(_newFacetAddress);
                ds.facetFunctionSelectors[_newFacetAddress].facetAddressPosition = uint16(facetAddressPosition);
            }
            // add or replace selectors
            for (uint256 selectorIndex; selectorIndex < _selectors.length; selectorIndex++) {
                bytes4 selector = _selectors[selectorIndex];
                address oldFacetAddress = ds.selectorToFacetAndPosition[selector].facetAddress;
                // add
                if (_action == IDiamondCut.FacetCutAction.Add) {
                    require(oldFacetAddress == address(0), "LibDiamondCut: Can't add function that already exists");
                    addSelector(_newFacetAddress, selector);
                } else if (_action == IDiamondCut.FacetCutAction.Replace) {
                    // replace
                    require(
                        oldFacetAddress != _newFacetAddress,
                        "LibDiamondCut: Can't replace function with same function"
                    );
                    removeSelector(oldFacetAddress, selector);
                    addSelector(_newFacetAddress, selector);
                } else {
                    revert("LibDiamondCut: Incorrect FacetCutAction");
                }
            }
        } else {
            require(
                _action == IDiamondCut.FacetCutAction.Remove,
                "LibDiamondCut: action not set to FacetCutAction.Remove"
            );
            // remove selectors
            for (uint256 selectorIndex; selectorIndex < _selectors.length; selectorIndex++) {
                bytes4 selector = _selectors[selectorIndex];
                removeSelector(ds.selectorToFacetAndPosition[selector].facetAddress, selector);
            }
        }
    }

    function addSelector(address _newFacet, bytes4 _selector) internal {
        LibDiamondStorage.DiamondStorage storage ds = LibDiamondStorage.diamondStorage();
        uint256 selectorPosition = ds.facetFunctionSelectors[_newFacet].functionSelectors.length;
        ds.facetFunctionSelectors[_newFacet].functionSelectors.push(_selector);
        ds.selectorToFacetAndPosition[_selector].facetAddress = _newFacet;
        ds.selectorToFacetAndPosition[_selector].functionSelectorPosition = uint16(selectorPosition);
    }

    function removeSelector(address _oldFacetAddress, bytes4 _selector) internal {
        LibDiamondStorage.DiamondStorage storage ds = LibDiamondStorage.diamondStorage();
        require(_oldFacetAddress != address(0), "LibDiamondCut: Can't remove or replace function that doesn't exist");
        // replace selector with last selector, then delete last selector
        uint256 selectorPosition = ds.selectorToFacetAndPosition[_selector].functionSelectorPosition;
        uint256 lastSelectorPosition = ds.facetFunctionSelectors[_oldFacetAddress].functionSelectors.length - 1;
        bytes4 lastSelector = ds.facetFunctionSelectors[_oldFacetAddress].functionSelectors[lastSelectorPosition];
        // if not the same then replace _selector with lastSelector
        if (lastSelector != _selector) {
            ds.facetFunctionSelectors[_oldFacetAddress].functionSelectors[selectorPosition] = lastSelector;
            ds.selectorToFacetAndPosition[lastSelector].functionSelectorPosition = uint16(selectorPosition);
        }
        // delete the last selector
        ds.facetFunctionSelectors[_oldFacetAddress].functionSelectors.pop();
        delete ds.selectorToFacetAndPosition[_selector];

        // if no more selectors for facet address then delete the facet address
        if (lastSelectorPosition == 0) {
            // replace facet address with last facet address and delete last facet address
            uint256 lastFacetAddressPosition = ds.facetAddresses.length - 1;
            address lastFacetAddress = ds.facetAddresses[lastFacetAddressPosition];
            uint256 facetAddressPosition = ds.facetFunctionSelectors[_oldFacetAddress].facetAddressPosition;
            if (_oldFacetAddress != lastFacetAddress) {
                ds.facetAddresses[facetAddressPosition] = lastFacetAddress;
                ds.facetFunctionSelectors[lastFacetAddress].facetAddressPosition = uint16(facetAddressPosition);
            }
            ds.facetAddresses.pop();
            delete ds.facetFunctionSelectors[_oldFacetAddress];
        }
    }

    function initializeDiamondCut(address _init, bytes memory _calldata) internal {
        if (_init == address(0)) {
            require(_calldata.length == 0, "LibDiamondCut: _init is address(0) but_calldata is not empty");
        } else {
            require(_calldata.length > 0, "LibDiamondCut: _calldata is empty but _init is not address(0)");
            if (_init != address(this)) {
                LibDiamondCut.ensureHasContractCode(_init, "LibDiamondCut: _init address has no code");
            }
            (bool success, bytes memory error) = _init.delegatecall(_calldata);
            if (!success) {
                if (error.length > 0) {
                    // bubble up the error
                    revert(string(error));
                } else {
                    revert("LibDiamondCut: _init function reverted");
                }
            }
        }
    }

    function ensureHasContractCode(address _contract, string memory _errorMessage) internal view {
        uint256 contractSize;
        assembly {
            contractSize := extcodesize(_contract)
        }
        require(contractSize > 0, _errorMessage);
    }
}




// SPDX-License-Identifier: MIT
pragma solidity 0.6.12;
pragma experimental ABIEncoderV2;

import { LibDiamondCut } from "./diamond/LibDiamondCut.sol";
import { DiamondFacet } from "./diamond/DiamondFacet.sol";
import { OwnershipFacet } from "./diamond/OwnershipFacet.sol";
import { LibDiamondStorage } from "./diamond/LibDiamondStorage.sol";
import { IDiamondCut } from "./diamond/IDiamondCut.sol";
import { IDiamondLoupe } from "./diamond/IDiamondLoupe.sol";
import { IERC165 } from "./diamond/IERC165.sol";
import { LibDiamondStorageDerivaDEX } from "./storage/LibDiamondStorageDerivaDEX.sol";
import { IDDX } from "./tokens/interfaces/IDDX.sol";

/**
 * @title DerivaDEX
 * @author DerivaDEX
 * @notice This is the diamond for DerivaDEX. All current
 *         and future logic runs by way of this contract.
 * @dev This diamond implements the Diamond Standard (EIP #2535).
 */
contract DerivaDEX {
    event OwnershipTransferred(address indexed previousOwner, address indexed newOwner);

    /**
     * @notice This constructor initializes the upgrade machinery (as
     *         per the Diamond Standard), sets the admin of the proxy
     *         to be the deploying address (very temporary), and sets
     *         the native DDX governance/operational token.
     * @param _ddxToken The native DDX token address.
     */
    constructor(IDDX _ddxToken) public {
        LibDiamondStorage.DiamondStorage storage ds = LibDiamondStorage.diamondStorage();
        LibDiamondStorageDerivaDEX.DiamondStorageDerivaDEX storage dsDerivaDEX =
            LibDiamondStorageDerivaDEX.diamondStorageDerivaDEX();

        // Temporarily set admin to the deploying address to facilitate
        // adding the Diamond functions
        dsDerivaDEX.admin = msg.sender;

        // Set DDX token address for token logic in facet contracts
        require(address(_ddxToken) != address(0), "DerivaDEX: ddx token is zero address.");
        dsDerivaDEX.ddxToken = _ddxToken;

        emit OwnershipTransferred(address(0), msg.sender);

        // Create DiamondFacet contract -
        // implements DiamondCut interface and DiamondLoupe interface
        DiamondFacet diamondFacet = new DiamondFacet();

        // Create OwnershipFacet contract which implements ownership
        // functions and supportsInterface function
        OwnershipFacet ownershipFacet = new OwnershipFacet();

        IDiamondCut.FacetCut[] memory diamondCut = new IDiamondCut.FacetCut[](2);

        // adding diamondCut function and diamond loupe functions
        diamondCut[0].facetAddress = address(diamondFacet);
        diamondCut[0].action = IDiamondCut.FacetCutAction.Add;
        diamondCut[0].functionSelectors = new bytes4[](6);
        diamondCut[0].functionSelectors[0] = DiamondFacet.diamondCut.selector;
        diamondCut[0].functionSelectors[1] = DiamondFacet.facetFunctionSelectors.selector;
        diamondCut[0].functionSelectors[2] = DiamondFacet.facets.selector;
        diamondCut[0].functionSelectors[3] = DiamondFacet.facetAddress.selector;
        diamondCut[0].functionSelectors[4] = DiamondFacet.facetAddresses.selector;
        diamondCut[0].functionSelectors[5] = DiamondFacet.supportsInterface.selector;

        // adding ownership functions
        diamondCut[1].facetAddress = address(ownershipFacet);
        diamondCut[1].action = IDiamondCut.FacetCutAction.Add;
        diamondCut[1].functionSelectors = new bytes4[](2);
        diamondCut[1].functionSelectors[0] = OwnershipFacet.transferOwnershipToSelf.selector;
        diamondCut[1].functionSelectors[1] = OwnershipFacet.getAdmin.selector;

        // execute internal diamondCut function to add functions
        LibDiamondCut.diamondCut(diamondCut, address(0), new bytes(0));

        // adding ERC165 data
        ds.supportedInterfaces[IERC165.supportsInterface.selector] = true;
        ds.supportedInterfaces[IDiamondCut.diamondCut.selector] = true;
        bytes4 interfaceID =
            IDiamondLoupe.facets.selector ^
                IDiamondLoupe.facetFunctionSelectors.selector ^
                IDiamondLoupe.facetAddresses.selector ^
                IDiamondLoupe.facetAddress.selector;
        ds.supportedInterfaces[interfaceID] = true;
    }

    // TODO(jalextowle): Remove this linter directive when
    // https://github.com/protofire/solhint/issues/248 is merged and released.
    /* solhint-disable ordering */
    receive() external payable {
        revert("DerivaDEX does not directly accept ether.");
    }

    // Finds facet for function that is called and executes the
    // function if it is found and returns any value.
    fallback() external payable {
        LibDiamondStorage.DiamondStorage storage ds;
        bytes32 position = LibDiamondStorage.DIAMOND_STORAGE_POSITION;
        assembly {
            ds_slot := position
        }
        address facet = ds.selectorToFacetAndPosition[msg.sig].facetAddress;
        require(facet != address(0), "Function does not exist.");
        assembly {
            calldatacopy(0, 0, calldatasize())
            let result := delegatecall(gas(), facet, 0, calldatasize(), 0, 0)
            let size := returndatasize()
            returndatacopy(0, 0, size)
            switch result
                case 0 {
                    revert(0, size)
                }
                default {
                    return(0, size)
                }
        }
    }
    /* solhint-enable ordering */
}


********************************KEVIN******************************
// SPDX-License-Identifier: MIT

pragma solidity ^0.6.0;

import "./IERC20.sol";
import "../../math/SafeMath.sol";
import "../../utils/Address.sol";

/**
 * @title SafeERC20
 * @dev Wrappers around ERC20 operations that throw on failure (when the token
 * contract returns false). Tokens that return no value (and instead revert or
 * throw on failure) are also supported, non-reverting calls are assumed to be
 * successful.
 * To use this library you can add a `using SafeERC20 for IERC20;` statement to your contract,
 * which allows you to call the safe operations as `token.safeTransfer(...)`, etc.
 */
library SafeERC20 {
    using SafeMath for uint256;
    using Address for address;

    function safeTransfer(IERC20 token, address to, uint256 value) internal {
        _callOptionalReturn(token, abi.encodeWithSelector(token.transfer.selector, to, value));
    }

    function safeTransferFrom(IERC20 token, address from, address to, uint256 value) internal {
        _callOptionalReturn(token, abi.encodeWithSelector(token.transferFrom.selector, from, to, value));
    }

    /**
     * @dev Deprecated. This function has issues similar to the ones found in
     * {IERC20-approve}, and its usage is discouraged.
     *
     * Whenever possible, use {safeIncreaseAllowance} and
     * {safeDecreaseAllowance} instead.
     */
    function safeApprove(IERC20 token, address spender, uint256 value) internal {
        // safeApprove should only be called when setting an initial allowance,
        // or when resetting it to zero. To increase and decrease it, use
        // 'safeIncreaseAllowance' and 'safeDecreaseAllowance'
        // solhint-disable-next-line max-line-length
        require((value == 0) || (token.allowance(address(this), spender) == 0),
            "SafeERC20: approve from non-zero to non-zero allowance"
        );
        _callOptionalReturn(token, abi.encodeWithSelector(token.approve.selector, spender, value));
    }

    function safeIncreaseAllowance(IERC20 token, address spender, uint256 value) internal {
        uint256 newAllowance = token.allowance(address(this), spender).add(value);
        _callOptionalReturn(token, abi.encodeWithSelector(token.approve.selector, spender, newAllowance));
    }

    function safeDecreaseAllowance(IERC20 token, address spender, uint256 value) internal {
        uint256 newAllowance = token.allowance(address(this), spender).sub(value, "SafeERC20: decreased allowance below zero");
        _callOptionalReturn(token, abi.encodeWithSelector(token.approve.selector, spender, newAllowance));
    }

    /**
     * @dev Imitates a Solidity high-level call (i.e. a regular function call to a contract), relaxing the requirement
     * on the return value: the return value is optional (but if data is returned, it must not be false).
     * @param token The token targeted by the call.
     * @param data The call data (encoded using abi.encode or one of its variants).
     */
    function _callOptionalReturn(IERC20 token, bytes memory data) private {
        // We need to perform a low level call here, to bypass Solidity's return data size checking mechanism, since
        // we're implementing it ourselves. We use {Address.functionCall} to perform this call, which verifies that
        // the target address contains contract code and also asserts for success in the low-level call.

        bytes memory returndata = address(token).functionCall(data, "SafeERC20: low-level call failed");
        if (returndata.length > 0) { // Return data is optional
            // solhint-disable-next-line max-line-length
            require(abi.decode(returndata, (bool)), "SafeERC20: ERC20 operation did not succeed");
        }
    }
}


// SPDX-License-Identifier: MIT
pragma solidity 0.6.12;
pragma experimental ABIEncoderV2;

import { LibDiamondStorageDerivaDEX } from "../../storage/LibDiamondStorageDerivaDEX.sol";
import { LibDiamondStoragePause } from "../../storage/LibDiamondStoragePause.sol";

/**
 * @title Pause
 * @author DerivaDEX
 * @notice This is a facet to the DerivaDEX proxy contract that handles
 *         the logic pertaining to pausing functionality. The purpose
 *         of this is to ensure the system can pause in the unlikely
 *         scenario of a bug or issue materially jeopardizing users'
 *         funds or experience. This facet will be removed entirely
 *         as the system stabilizes shortly. It's important to note that
 *         unlike the vast majority of projects, even during this
 *         short-lived period of time in which the system can be paused,
 *         no single admin address can wield this power, but rather
 *         pausing must be carried out via governance.
 */
contract Pause {
    event PauseInitialized();

    event IsPausedSet(bool isPaused);

    /**
     * @notice Limits functions to only be called via governance.
     */
    modifier onlyAdmin {
        LibDiamondStorageDerivaDEX.DiamondStorageDerivaDEX storage dsDerivaDEX =
            LibDiamondStorageDerivaDEX.diamondStorageDerivaDEX();
        require(msg.sender == dsDerivaDEX.admin, "Pause: must be called by Gov.");
        _;
    }

    /**
     * @notice This function initializes the facet.
     */
    function initialize() external onlyAdmin {
        emit PauseInitialized();
    }

    /**
     * @notice This function sets the paused status.
     * @param _isPaused Whether contracts are paused or not.
     */
    function setIsPaused(bool _isPaused) external onlyAdmin {
        LibDiamondStoragePause.DiamondStoragePause storage dsPause = LibDiamondStoragePause.diamondStoragePause();

        dsPause.isPaused = _isPaused;

        emit IsPausedSet(_isPaused);
    }

    /**
     * @notice This function gets whether the contract ecosystem is
     *         currently paused.
     * @return Whether contracts are paused or not.
     */
    function getIsPaused() public view returns (bool) {
        LibDiamondStoragePause.DiamondStoragePause storage dsPause = LibDiamondStoragePause.diamondStoragePause();

        return dsPause.isPaused;
    }
}


