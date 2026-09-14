/*
	This file is part of solidity.

	solidity is free software: you can redistribute it and/or modify
	it under the terms of the GNU General Public License as published by
	the Free Software Foundation, either version 3 of the License, or
	(at your option) any later version.

	solidity is distributed in the hope that it will be useful,
	but WITHOUT ANY WARRANTY; without even the implied warranty of
	MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
	GNU General Public License for more details.

	You should have received a copy of the GNU General Public License
	along with solidity.  If not, see <http://www.gnu.org/licenses/>.
*/
// SPDX-License-Identifier: GPL-3.0
/**
 * Some useful snippets for the optimiser.
 */

#include <libyul/Utilities.h>

#include <libyul/backends/evm/EVMDialect.h>

#include <libyul/AST.h>
#include <libyul/Dialect.h>
#include <libyul/Exceptions.h>

#include <libsolutil/CommonData.h>
#include <libsolutil/FixedHash.h>
#include <libsolutil/Visitor.h>

#include <algorithm>
#include <string_view>

using namespace solidity;
using namespace solidity::yul;
using namespace solidity::util;

std::string solidity::yul::reindent(std::string const& _code)
{
	int constexpr indentationWidth = 4;

	auto constexpr static countBraces = [](std::string_view _s) noexcept -> int
	{
		_s = _s.substr(0, _s.find("//"));
		auto const opening = std::count_if(_s.begin(), _s.end(), [](auto ch) { return ch == '{' || ch == '('; });
		auto const closing = std::count_if(_s.begin(), _s.end(), [](auto ch) { return ch == '}' || ch == ')'; });
		return int(opening - closing);
	};
	// Same character set as boost::trim in the classic locale.
	auto constexpr static trim = [](std::string_view _s) noexcept -> std::string_view
	{
		auto const first = _s.find_first_not_of(" \t\n\v\f\r");
		if (first == std::string_view::npos)
			return {};
		return _s.substr(first, _s.find_last_not_of(" \t\n\v\f\r") - first + 1);
	};

	std::string out;
	out.reserve(_code.size());
	std::string_view code = _code;
	int depth = 0;
	bool previousEmpty = false;
	while (true)
	{
		size_t const lineEnd = code.find('\n');
		std::string_view const line = trim(code.substr(0, lineEnd));

		// Reduce multiple consecutive empty lines.
		if (!(line.empty() && previousEmpty))
		{
			int const diff = countBraces(line);
			if (diff < 0)
				depth += diff;

			if (!line.empty())
			{
				out.append(static_cast<size_t>(std::max(depth * indentationWidth, 0)), ' ');
				out.append(line);
			}
			out += '\n';

			if (diff > 0)
				depth += diff;
		}
		previousEmpty = line.empty();

		if (lineEnd == std::string_view::npos)
			break;
		code.remove_prefix(lineEnd + 1);
	}

	return out;
}

LiteralValue solidity::yul::valueOfNumberLiteral(std::string_view const _literal)
{
	return LiteralValue{LiteralValue::Data(_literal), std::string(_literal)};
}

LiteralValue solidity::yul::valueOfStringLiteral(std::string_view const _literal)
{
	std::string const s(_literal);
	return LiteralValue{u256(h256(s, h256::FromBinary, h256::AlignLeft)), s};
}

LiteralValue solidity::yul::valueOfBuiltinStringLiteralArgument(std::string_view _literal)
{
	return LiteralValue{std::string(_literal)};
}

LiteralValue solidity::yul::valueOfBoolLiteral(std::string_view const _literal)
{
	if (_literal == "true")
		return LiteralValue{true};
	else if (_literal == "false")
		return LiteralValue{false};

	yulAssert(false, "Unexpected bool literal value!");
}

LiteralValue solidity::yul::valueOfLiteral(std::string_view const _literal, LiteralKind const& _kind, bool const _unlimitedLiteralArgument)
{
	switch (_kind)
	{
	case LiteralKind::Number:
		return valueOfNumberLiteral(_literal);
	case LiteralKind::Boolean:
		return valueOfBoolLiteral(_literal);
	case LiteralKind::String:
		return _unlimitedLiteralArgument ? valueOfBuiltinStringLiteralArgument(_literal) : valueOfStringLiteral(_literal);
	}
	util::unreachable();
}

std::string solidity::yul::formatLiteral(solidity::yul::Literal const& _literal, bool const _validated)
{
	if (_validated)
		yulAssert(validLiteral(_literal), "Encountered invalid literal in formatLiteral.");

	if (_literal.value.unlimited())
		return _literal.value.builtinStringLiteralValue();

	if (_literal.value.hint())
		return *_literal.value.hint();

	if (_literal.kind == LiteralKind::Boolean)
		return _literal.value.value() == false ? "false" : "true";

	// if there is no hint and it is not a boolean, just stringify the u256 word
	return _literal.value.value().str();
}

bool solidity::yul::validLiteral(solidity::yul::Literal const& _literal)
{
	switch (_literal.kind)
	{
	case LiteralKind::Number:
		return validNumberLiteral(_literal);
	case LiteralKind::Boolean:
		return validBoolLiteral(_literal);
	case LiteralKind::String:
		return validStringLiteral(_literal);
	}
	util::unreachable();
}

bool solidity::yul::validStringLiteral(solidity::yul::Literal const& _literal)
{
	if (_literal.kind != LiteralKind::String)
		return false;

	if (_literal.value.unlimited())
		return true;

	if (_literal.value.hint())
		return _literal.value.hint()->size() <= 32 && _literal.value.value() == valueOfLiteral(*_literal.value.hint(), _literal.kind).value();

	return true;
}

bool solidity::yul::validNumberLiteral(solidity::yul::Literal const& _literal)
{
	if (_literal.kind != LiteralKind::Number || _literal.value.unlimited())
		return false;

	if (!_literal.value.hint())
		return true;

	auto const& repr = *_literal.value.hint();

	if (!isValidDecimal(repr) && !isValidHex(repr))
		return false;

	if (bigint(repr) > u256(-1))
		return false;

	if (_literal.value.value() != valueOfLiteral(repr, _literal.kind).value())
		return false;

	return true;
}

bool solidity::yul::validBoolLiteral(solidity::yul::Literal const& _literal)
{
	if (_literal.kind != LiteralKind::Boolean || _literal.value.unlimited())
		return false;

	if (_literal.value.hint() && !(*_literal.value.hint() == "true" || *_literal.value.hint() == "false"))
		return false;

	yulAssert(u256(0) == u256(false));
	yulAssert(u256(1) == u256(true));

	if (_literal.value.hint())
	{
		if (*_literal.value.hint() == "false")
			return _literal.value.value() == false;
		else
			return _literal.value.value() == true;
	}

	return _literal.value.value() == true || _literal.value.value() == false;
}

template<>
bool Less<Literal>::operator()(Literal const& _lhs, Literal const& _rhs) const
{
	if (_lhs.kind != _rhs.kind)
		return _lhs.kind < _rhs.kind;

	if (_lhs.value.unlimited() && _rhs.value.unlimited())
		yulAssert(
			_lhs.kind == LiteralKind::String && _rhs.kind == LiteralKind::String,
			"Cannot have unlimited value that is not of String kind."
		);

	return _lhs.value < _rhs.value;

}

bool SwitchCaseCompareByLiteralValue::operator()(Case const* _lhs, Case const* _rhs) const
{
	yulAssert(_lhs && _rhs, "");
	return Less<Literal*>{}(_lhs->value.get(), _rhs->value.get());
}

std::string_view yul::resolveFunctionName(FunctionName const& _functionName, Dialect const& _dialect)
{
	GenericVisitor visitor{
		[&](Identifier const& _identifier) -> std::string const& { return _identifier.name.str(); },
		[&](BuiltinName const& _builtin) -> std::string const& { return _dialect.builtin(_builtin.handle).name; }
	};
	return std::visit(visitor, _functionName);
}

std::string_view yul::resolveFunctionName(FunctionHandle const& _functionHandle, Dialect const& _dialect)
{
	GenericVisitor visitor{
		[&](YulName const& _name) -> std::string const& { return _name.str(); },
		[&](BuiltinHandle const& _handle) -> std::string const& { return _dialect.builtin(_handle).name; }
	};
	return std::visit(visitor, _functionHandle);
}

BuiltinFunction const* yul::resolveBuiltinFunction(FunctionName const& _functionName, Dialect const& _dialect)
{
	GenericVisitor visitor{
		[&](Identifier const&) -> BuiltinFunction const* { return nullptr; },
		[&](BuiltinName const& _builtin) -> BuiltinFunction const* { return &_dialect.builtin(_builtin.handle); }
	};
	return std::visit(visitor, _functionName);
}

BuiltinFunctionForEVM const* yul::resolveBuiltinFunctionForEVM(FunctionName const& _functionName, EVMDialect const& _dialect)
{
	GenericVisitor visitor{
		[&](Identifier const&) -> BuiltinFunctionForEVM const* { return nullptr; },
		[&](BuiltinName const& _builtin) -> BuiltinFunctionForEVM const* { return &_dialect.builtin(_builtin.handle); }
	};
	return std::visit(visitor, _functionName);
}

FunctionHandle yul::functionNameToHandle(FunctionName const& _functionName)
{
	GenericVisitor visitor{
		[&](Identifier const& _identifier) -> FunctionHandle { return _identifier.name; },
		[&](BuiltinName const& _builtin) -> FunctionHandle { return _builtin.handle; }
	};
	return std::visit(visitor, _functionName);
}

